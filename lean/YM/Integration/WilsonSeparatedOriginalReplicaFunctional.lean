import YM.Integration.WilsonSeparatedOriginalReplicaMeasure

/-! The signed three-point measurement is a linear experiment on the common test of three copies. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalReplicaFunctional
open MeasureTheory Set Finset WilsonSeparatedOriginalReplicaMeasure
open scoped Classical BigOperators Topology
variable {A:Type*}[TopologicalSpace A]

private def selection (t:Fin 3→Fin 3)(U:A×A×A):Fin 3 → A:=fun i=>![U.1,U.2.1,U.2.2] (t i)

private theorem coordinate (i:Fin 3):Continuous (fun U:A×A×A=>![U.1,U.2.1,U.2.2] i):=by
  fin_cases i
  · exact continuous_fst
  · exact continuous_fst.comp continuous_snd
  · exact continuous_snd.comp continuous_snd

private theorem selected (t:Fin 3→Fin 3):Continuous (selection (A:=A) t):=
  continuous_pi (fun i=>coordinate (t i))

variable [MeasurableSpace A][CompactSpace A][SecondCountableTopology A][OpensMeasurableSpace A]
variable (μ:Measure A)[IsProbabilityMeasure μ]

private def experiment (t:Fin 3→Fin 3):C(Fin 3 → A,ℂ)→ₗ[ℂ] ℂ where
  toFun F:=∫U,F (selection t U) ∂μ.prod (μ.prod μ)
  map_add' F H:=by
    change (∫U,F (selection t U)+H (selection t U) ∂μ.prod (μ.prod μ))=_
    exact integral_add ((F.continuous.comp (selected t)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((H.continuous.comp (selected t)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' c F:=by
    change (∫U,c*F (selection t U) ∂μ.prod (μ.prod μ))=c*_
    exact integral_const_mul ..

def listener : C(Fin 3 → A,ℂ) →ₗ[ℂ] ℂ:=
  experiment μ ![0,0,0]-(experiment μ ![0,0,1]+experiment μ ![0,1,0]+experiment μ ![1,0,0])+
    (2:ℂ) • experiment μ ![0,1,2]

private theorem nested (F:A×A×A→ℂ)(hc:Continuous F):
    (∫U,F U ∂μ.prod (μ.prod μ))=∫a,∫b,∫c,F (a,b,c) ∂μ ∂μ ∂μ:=by
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae;filter_upwards with a
  apply integral_prod
  exact (hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem recorded (t:Fin 3→Fin 3)(F:C(Fin 3 → A,ℂ)):
    experiment μ t F=∫a,∫b,∫c,F (selection t (a,b,c)) ∂μ ∂μ ∂μ:=
  nested μ _ (F.continuous.comp (selected t))

theorem measured (F:C(Fin 3 → A,ℂ)):listener μ F=read μ F:=by
  simp only [listener,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,recorded]
  have abc (a b c:A):selection ![0,1,2] (a,b,c)=![a,b,c]:=by ext i;fin_cases i <;>rfl
  have aaa (a b c:A):selection ![0,0,0] (a,b,c)=![a,a,a]:=by ext i;fin_cases i <;>rfl
  have aab (a b c:A):selection ![0,0,1] (a,b,c)=![a,a,b]:=by ext i;fin_cases i <;>rfl
  have aba (a b c:A):selection ![0,1,0] (a,b,c)=![a,b,a]:=by ext i;fin_cases i <;>rfl
  have baa (a b c:A):selection ![1,0,0] (a,b,c)=![b,a,a]:=by ext i;fin_cases i <;>rfl
  simp_rw [abc,aaa,aab,aba,baa];simp [WilsonSeparatedOriginalReplicaMeasure.read]

end YM.Integration.WilsonSeparatedOriginalReplicaFunctional
