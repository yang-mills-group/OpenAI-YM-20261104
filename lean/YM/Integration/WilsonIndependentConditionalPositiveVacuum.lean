import YM.Integration.WilsonIndependentConditionalVacuum

/-! The positive-rank Notebook read at the retained field is the common
free quadratic form less the true Wilson successor, with the vacuum scalar
removed only at the end. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentConditionalPositiveVacuum
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Diagram
open PertExtension PowerSeries FreeResolvent Lattice RG Wilson Tree Precision Matrix Exterior Metric
open WilsonIndependentConditionalDiagramResponse WilsonIndependentConditionalVacuum
open WilsonIndependentConditionalScalarConvention
open scoped Classical BigOperators MatrixOrder

def value {U:Type}(p:Ink U)(e:ℕ)(v:Lawn U):ℝ:=
  MvPolynomial.eval v (coeff e p)-MvPolynomial.eval (0:Lawn U) (coeff e p)

private theorem heated_agree {I:Type}(K:Budget.Layer I I)(V:Orders I)(s t:Bool):
    Positive (ceaseHeat K V s) (ceaseHeat K V t):=by
  intro e r hr;unfold ceaseHeat heated
  exact Finset.sum_congr rfl fun k _=>positive K (V:=V) (U:=V) (fun _ _ _=>rfl) s t k e r hr

private theorem delta {I J:Type}[Fintype I][Fintype J](T U:Ranked (I⊕J))
    (h:∀r,0<r→T r=U r)(d:ℕ)(v:Lawn J):
    MvPolynomial.eval v (projectZeroPoly I J (packed T d))-
        MvPolynomial.eval (0:Lawn J) (projectZeroPoly I J (packed T d))=
    MvPolynomial.eval v (projectZeroPoly I J (packed U d))-
        MvPolynomial.eval (0:Lawn J) (projectZeroPoly I J (packed U d)):=by
  simp only [packed,map_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  cases r with
  | succ r=>rw [h _ (by omega)]
  | zero=>simp [render,word,projectZeroPoly]

private theorem soil_constant {I:Type}(p:Cost)(e:ℕ)(v:Lawn I):value (soil p) e v=0:=by
  simp [value,soil,coeff_map]

variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)(H Y:FaceRow)
  (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

theorem original {Ñ:ChartRatio G}{P:PChart G f}(p:shellK 2 P)(ratio:LocalRatio Ñ)
    (branch:S.patch.Branches S.kernel G)(sym:(H.acts f).transpose=H.acts f)
    (pure:∀ i,Pure (P i))(hf:(treeMatrix G S F H).PosDef)(e:ℕ)(b:TreeVars G c):
    value (projectZero (rated (fun i=>i+2) (ceaseHeat (lines S F H) (old S F Q Ñ P) false))) e b =
    value (orbC (precisionC G c Y)) e b-value (flash (winter S F H Y Q Ñ P)) e b:=by
  let V:= old S F Q Ñ P
  let K:= lines (G:=G) S F H
  have cc:value (projectZero (rated (fun i=>i+2) (ceaseHeat K V false))) e b=
      value (projectZero (raw S F H Q Ñ P)) e b:=by
    simp only [value,projectZero,raw,rated,coeff_map,coeff_mk]
    exact delta _ _ (heated_agree K V false true e) _ _
  change value (projectZero (rated _ (ceaseHeat K V false))) e b=_
  rw [cc,WilsonIndependentConditionalVacuum.original S F H Q p ratio branch sym pure hf]
  have h₁:=flat_count (precisionC G c Y)
  have h₂:=summer_band S F H Q ratio p
  have h₃:=uband_length (plugζ S Ñ) (U:=Woods G c) 2
  rw [winter,flash_add (finite_shell (shell_sub h₁ h₂)) (finite_shell h₃),
    flash_sub (finite_shell h₁) (finite_shell h₂),flat_flash,uband_flash]
  have hc:=soil_constant (plugζ S Ñ) e b
  simp only [value,map_add,map_sub] at hc ⊢
  linarith

end YM.Integration.WilsonIndependentConditionalPositiveVacuum
