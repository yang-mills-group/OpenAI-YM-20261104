import YM.Integration.WilsonRegisteredAxialConditional

/-! Variance of a signed complex insertion under one actual probability. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalComplexVariance
open MeasureTheory Filter
open scoped Topology

private def pairing (b:ℂ):ℂ→L[ℝ]ℝ := b.re • Complex.reCLM + b.im • Complex.imCLM

private theorem diagonal (b:ℂ):pairing b b=‖b‖^2:=by
  simp [pairing,Complex.sq_norm,Complex.normSq_apply]

private theorem subtract (a b:ℂ):‖a-b‖^2=‖a‖^2-2*pairing b a+‖b‖^2:=by
  simp [pairing,Complex.sq_norm,Complex.normSq_apply]
  ring

theorem original {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω} [IsProbabilityMeasure μ]
    {B:Ω→ℂ} (income:MemLp B 2 μ):
    let mean:=∫U,B U ∂μ
    (∫U,‖B U-mean‖^2 ∂μ)=(∫U,‖B U‖^2 ∂μ)-‖mean‖^2:=by
  intro mean
  have b:Integrable B μ:=income.integrable (by norm_num)
  have sq:Integrable (fun U=>‖B U‖^2) μ:=income.norm.integrable_sq
  have mixed:=((pairing mean).integrable_comp b).const_mul 2
  calc
    _ = ∫U,‖B U‖^2-2*pairing mean (B U)+‖mean‖^2 ∂μ:=
      integral_congr_ae (ae_of_all _ fun U=>subtract (B U) mean)
    _ = _:=by
      have centered:Integrable (fun U=>‖B U‖^2-2*pairing mean (B U)) μ:=sq.sub mixed
      rw [integral_add centered (integrable_const (‖mean‖^2)),integral_sub sq mixed,integral_const_mul,
        (pairing mean).integral_comp_comm b]
      change _-2*pairing mean mean+_=_
      rw [diagonal]
      simp
      ring

end YM.Integration.WilsonPhysicalComplexVariance
