import YM.MSbar.Mosaic.Cue
import YM.MSbar.Lease.Ticket

/-! The genuine coarse thermal collar; its payment only uses the original
measured inverse-temperature band and the exact logarithmic room. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionChartRoom
open Filter RG MSbar MSbar.Mosaic MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage

theorem room_price (D:ℝ) (hD:0 ≤ D):
    ∀ᶠ y:ℝ in atTop,∀ g:ℝ,Mosaic.lensT y g → D ≤ room y/g := by
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2*D))]
    with y hy logs g band
  have log₁:1 ≤ Real.log y:=(le_max_left ..).trans logs
  have sqrt₁:1 ≤ Real.sqrt (Real.log y):=by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt log₁
  have cue₀:0 < cue y:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hy))
  have g₀:0 < g:=(half_pos cue₀).trans_le band.1
  have eq:y^(-(1/2:ℝ))=cue y:=by rw [Real.rpow_neg (zero_le_one.trans hy.le),←Real.sqrt_eq_rpow];rfl
  apply (le_div_iff₀ g₀).mpr
  calc D*g ≤ D*(2*cue y) :=mul_le_mul_of_nonneg_left band.2 hD
       _ = cue y*(2*D) := by ring
       _ ≤ cue y*Real.log y := mul_le_mul_of_nonneg_left ((le_max_right ..).trans logs) cue₀.le
       _ ≤ cue y*Real.log y*Real.sqrt (Real.log y) := le_mul_of_one_le_right (mul_nonneg cue₀.le (zero_le_one.trans log₁)) sqrt₁
       _ = room y := by rw [MSbar.Heath.Cottage.room,MSbar.Heath.Stock.distance,eq]

end YM.Integration.WilsonPosteriorProjectionChartRoom
end
