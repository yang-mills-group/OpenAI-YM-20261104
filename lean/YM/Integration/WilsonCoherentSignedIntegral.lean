import YM.Integration.WilsonCoherentRegisteredFibre

/-! An integrable signed cofactor can multiply the change of a genuine
integral. The Taylor polynomial needs only measurability on the same law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentSignedIntegral
open Filter Set MeasureTheory

theorem comparison {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω} {H F P:Ω→ℝ} {K:ℝ}
    (hH:Integrable H μ) (income:Integrable (fun x=>H x*F x) μ)
    (old:AEStronglyMeasurable F μ) (filed:AEStronglyMeasurable P μ)
    (bound:∀ᵐ x ∂μ,‖F x-P x‖≤K) :
    |(∫x,H x*F x ∂μ)-(∫x,H x*P x ∂μ)|≤ K*∫x,|H x| ∂μ := by
  have paid:∀ᵐ x ∂μ,‖H x*(F x-P x)‖≤K*‖H x‖:=by
    filter_upwards [bound] with x hx
    rw [norm_mul,mul_comm K]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  have e:Integrable (fun x=>H x*(F x-P x)) μ :=
    (hH.norm.const_mul K).mono' (hH.aestronglyMeasurable.mul (old.sub filed)) paid
  have hP:Integrable (fun x=>H x*P x) μ:=(income.sub e).congr (ae_of_all _ fun x=>by dsimp;ring)
  rw [←integral_sub income hP,←integral_const_mul]
  have hdiff:∀ᵐ x ∂μ,‖H x*F x-H x*P x‖≤K*‖H x‖:=by
    simpa only [←mul_sub] using paid
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le (f:=fun x=>H x*F x-H x*P x) (hH.norm.const_mul K) hdiff)

end YM.Integration.WilsonCoherentSignedIntegral
