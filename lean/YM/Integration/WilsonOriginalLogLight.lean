import YM.Integration.WilsonOriginalHighLightCalendar

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalLogLight

open Filter
open scoped Topology

theorem movable : Stationary.Movable Real.log where
  grows := Real.tendsto_log_atTop
  relaxes c hc := by
    filter_upwards [eventually_ge_atTop (max 2 c)] with x hx
    have h₂ : 2 ≤ x := (le_max_left ..).trans hx
    have hc' : c ≤ x := (le_max_right ..).trans hx
    have hp : 0 < x := by linarith
    have h : x + c ≤ x * x := by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h₂)]
    have bound := Real.log_le_log (show 0 < x+c by linarith) h
    rw [Real.log_mul hp.ne' hp.ne'] at bound
    linarith
  cap θ hθ := by
    have growth : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    filter_upwards [growth.eventually_ge_atTop (1 / θ), eventually_gt_atTop (1 : ℝ)] with x hy hx
    have hp := Real.log_pos hx
    have ht : 0 ≤ Real.log (Real.log x) := (by positivity : 0 ≤ 1 / θ).trans hy
    have hg := (div_le_iff₀ hθ).mp hy
    have h : Real.log (Real.log x) ≤ Real.log (Real.log x) ^ 2 * θ := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hg)]
    calc
      Real.log x = Real.exp (Real.log (Real.log x)) := (Real.exp_log hp).symm
      _ ≤ Real.exp (Real.log (Real.log x) ^ 2 * θ) := Real.exp_le_exp.mpr h
      _ = (Real.exp (Real.log (Real.log x) ^ 2)) ^ θ := Real.exp_mul ..
      _ ≤ 2 * (Real.exp (Real.log (Real.log x) ^ 2)) ^ θ := by
        nlinarith [Real.rpow_pos_of_pos (Real.exp_pos (Real.log (Real.log x) ^ 2)) θ]

end YM.Integration.WilsonOriginalLogLight
end
