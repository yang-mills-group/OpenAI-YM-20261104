import YM.Integration.WilsonMovingForkSignedSamples
import YM.Integration.WilsonPublicForkTestProduct
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! A supported signed quadrature of the actual one- or two-profile
physical measurement, simultaneously for the preselected finite kernels. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkProfileSamples
open Filter Finset Set MeasureTheory FVA2.O
open WilsonPublicForkTestProduct
open scoped Classical BigOperators ENNReal

private theorem compact {A I:Type}[MeasurableSpace A][TopologicalSpace A][T2Space A][BorelSpace A]
    [Fintype I](μ:Measure A)[IsFiniteMeasureOnCompacts μ](s:Set A)(cs:IsCompact s)
    (den:A→ℂ)(dc:ContinuousOn den s)(outside:∀x,x∉s→den x=0)
    (F:I→A→ℂ)(regular:∀i,ContinuousOn (F i) s){ε:ℝ}(ep:0<ε):
    ∃ι:Type,∃_:Fintype ι,∃x:ι→s,∃m:ι→ℂ,∑i,‖m i‖≤(∫a,‖den a‖ ∂μ)+ε ∧
      ∀j:I,‖(∫a,den a*F j a ∂μ)-∑i,m i*F j (x i)‖≤ε:=by
  letI:IsFiniteMeasure (μ.restrict s):=isFiniteMeasure_restrict.mpr cs.measure_lt_top.ne
  let row:=fun a i=>F i a
  have paid(i:I):Integrable (fun a=>den a*F i a) (μ.restrict s):=
    (dc.mul (regular i)).integrableOn_compact cs
  have normed:Integrable (fun a=>‖den a‖) (μ.restrict s):=dc.norm.integrableOn_compact cs
  have bank:Integrable (fun a=>den a • row a) (μ.restrict s):=Integrable.of_eval paid
  obtain ⟨ι,finite,x,m,cost,bound⟩:=WilsonMovingForkSignedSamples.original (μ.restrict s) s
    (ae_restrict_mem cs.measurableSet) den row normed bank ep
  refine ⟨ι,finite,x,m,?_,?_⟩
  · have eq:=setIntegral_eq_integral_of_forall_compl_eq_zero (μ:=μ) (s:=s)
      (f:=fun a=>‖den a‖) (fun a ha=>by rw [outside a ha,norm_zero])
    rwa [eq] at cost
  · intro i
    have price:‖((∫a,den a • row a ∂μ.restrict s)-∑k,m k • row (x k)) i‖≤ε:=(norm_le_pi_norm _ i).trans bound
    have cut:=setIntegral_eq_integral_of_forall_compl_eq_zero (μ:=μ) (s:=s)
      (f:=fun a=>den a*F i a) (fun a ha=>by rw [outside a ha,zero_mul])
    have projected:((∫a,den a • row a ∂μ.restrict s) i)=(∫a,den a*F i a ∂μ.restrict s):=
      eval_integral (f:=fun a=>den a • row a) (fun j=>paid j) i
    rw [Pi.sub_apply,projected,cut] at price
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,row] using price

theorem joint {n l:ℕ}{I:Type}[Fintype I](ψ:Test n)(φ:Test l)(F:I→Points n×Points l→ℂ)
    (regular:∀i,ContinuousOn (F i) (space ψ φ)){ε:ℝ}(ep:0<ε):
    ∃ι:Type,∃_:Fintype ι,∃x:ι→space ψ φ,∃m:ι→ℂ,∑i,‖m i‖≤Read.Value ψ*Read.Value φ+ε ∧
      ∀j:I,‖tested ψ φ (F j)-∑i,m i*F j (x i)‖≤ε:=by
  let den:=fun p:Points n×Points l=>ψ p.1*φ p.2
  have outside(p:Points n×Points l)(miss:p∉space ψ φ):den p=0:=by
    by_cases hx:p.1∈tsupport ψ
    · have hz:p.2∉tsupport φ:=fun inside=>miss ⟨hx,inside⟩
      simp [den,image_eq_zero_of_notMem_tsupport hz]
    · simp [den,image_eq_zero_of_notMem_tsupport hx]
  have cont:Continuous den:=(ψ.continuous.comp continuous_fst).mul (φ.continuous.comp continuous_snd)
  have mass:(∫p,‖den p‖)=Read.Value ψ*Read.Value φ:=by
    simp only [den,norm_mul];exact integral_prod_mul (μ:=volume) (ν:=volume) (fun x=>‖ψ x‖) (fun z=>‖φ z‖)
  simpa only [mass,tested,den] using compact volume (space ψ φ) (ψ.hasCompactSupport.prod φ.hasCompactSupport)
    den cont.continuousOn outside F regular ep

theorem one {n:ℕ}{I:Type}[Fintype I](φ:Test n)(F:I→Points n→ℂ)
    (regular:∀i,ContinuousOn (F i) (tsupport φ)){ε:ℝ}(ep:0<ε):
    ∃ι:Type,∃_:Fintype ι,∃x:ι→tsupport φ,∃m:ι→ℂ,∑i,‖m i‖≤Read.Value φ+ε ∧
      ∀j:I,‖φ.applyTo (F j)-∑i,m i*F j (x i)‖≤ε:=
  compact volume (tsupport φ) φ.hasCompactSupport φ φ.continuous.continuousOn
    (fun _=>image_eq_zero_of_notMem_tsupport) F regular ep

end YM.Integration.WilsonMovingForkProfileSamples
end
