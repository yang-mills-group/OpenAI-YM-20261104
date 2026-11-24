import YM.Integration.FVA1Physical.Wilson.FluctuationFieldRows
import YM.Integration.FVA1Physical.Wilson.HotelBudget
import YM.Integration.FVA1Physical.Round2.FieldSharpClock

/-! Evaluating a fixed polynomial on the actual thermal-width chart costs less
than any positive order of the measured coupling, independently of the torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter MSbar MSbar.Mosaic MSbar.Heath.Cottage
open YM.Integration.FVA1Physical.Wilson
open scoped Topology

theorem thermal_reset_gain (m p:ℕ) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) (hp:η < (p:ℝ)+1) :
    ∀ᶠ y:ℝ in atTop,∀ h:ℝ, lensT y h →
      h^((p:ℝ)+1-η/2)*(1+max 0 (D*room y/h))^(m+1) ≤ h^((p:ℝ)+1-η) := by
  have rise:Tendsto (fun y:ℝ=>y) atTop atTop:=tendsto_id
  have fees:=Run.Ypow rise (Run.stanza rise) (m+1)
  filter_upwards [hotel_scalar 0 D le_rfl hD,fees (η/16) (by positivity),
    Alto.broad.eventually_ge_atTop 2,field_sharp_clock p 0 le_rfl (half_pos hη) (by linarith only [hp,hη]),
    eventually_gt_atTop (0:ℝ)] with y budget cash high price pos
  intro h band
  have hg := (half_pos (inv_pos.mpr (Real.sqrt_pos.mpr pos))).trans_le band.1
  have window : D*room y/h ≤ hatW y/32 := by
    apply (div_le_iff₀ hg).mpr
    simpa only [zero_mul,zero_add,vol,mul_comm h] using budget h band
  have one : 1+max 0 (D*room y/h) ≤ hatW y := by
    have upper : max 0 (D*room y/h) ≤ hatW y-1 := max_le (by linarith only [high]) (window.trans (by linarith only [high]))
    linarith only [upper]
  have exp : (1+max 0 (D*room y/h))^(m+1) ≤ y^(η/16) :=
    (pow_le_pow_left₀ (by positivity) one _).trans ((le_abs_self _).trans cash)
  have amount:=price h band
  rw [zero_mul,add_zero,show η/2/8=η/16 by ring] at amount
  have reserve : h^(p+1)*y^(η/16) ≤ h^((p:ℝ)+1-η/2) := by
    nlinarith only [amount,Real.rpow_nonneg pos.le (Mosaic.pawn (p+2)),
      mul_nonneg (pow_nonneg hg.le (p+1)) (Real.rpow_nonneg pos.le (η/16))]
  have reserve' : h^((p:ℝ)+1)*y^(η/16) ≤ h^((p:ℝ)+1-η/2) := by
    simpa only [←Nat.cast_add_one,Real.rpow_natCast] using reserve
  calc
    _ ≤ h^((p:ℝ)+1-η/2)*y^(η/16) := mul_le_mul_of_nonneg_left exp (Real.rpow_nonneg hg.le _)
    _ = h^(-η/2)*(h^((p:ℝ)+1)*y^(η/16)) := by
      rw [←mul_assoc,←Real.rpow_add hg];congr 2;ring
    _ ≤ h^(-η/2)*h^((p:ℝ)+1-η/2) := mul_le_mul_of_nonneg_left reserve' (Real.rpow_nonneg hg.le _)
    _ = _ := by rw [←Real.rpow_add hg];congr 1;ring

end YM.Integration.FVA1Physical.Round2.Curvature
