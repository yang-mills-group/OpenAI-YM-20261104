import YM.Integration.WilsonOriginalTestedFourierBank
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTemperatureDecay
open Filter Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology
theorem original {G : Gauge} {warm : ℝ → ℝ} (paid : Coupling G warm) :
    Tendsto warm trail (𝓝 0)  := by
  have logs : Tendsto LogV trail atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have invLog := tendsto_inv_atTop_zero.comp logs
  have sq : Tendsto (fun r => warm r^2) trail (𝓝 0) := by
    have h := invLog.mul paid.running
    rw [zero_mul] at h
    apply h.congr'
    filter_upwards [logs.eventually (eventually_gt_atTop 0)] with r pos
    change (LogV r)⁻¹ * (LogV r * warm r^2) = warm r^2
    rw [← mul_assoc,inv_mul_cancel₀ pos.ne',one_mul]
  have absValue := (Real.continuous_sqrt.tendsto 0).comp sq
  rw [Real.sqrt_zero] at absValue
  apply absValue.congr'
  filter_upwards [paid.positive] with r hr
  exact Real.sqrt_sq hr.le
end YM.Integration.WilsonOriginalTemperatureDecay
