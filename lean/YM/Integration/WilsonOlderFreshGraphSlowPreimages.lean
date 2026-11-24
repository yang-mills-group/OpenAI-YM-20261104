import YM.Integration.WilsonOlderFreshGraphFinePreimages
import YM.Integration.WilsonWindowReportingPace

/-! On the elected slow calendar the entire physical cost of all affine
children in a single dated normalized-column comparison is subpower at that
same date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphSlowPreimages
open Function Filter Finset Lattice Real RG Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
  (slow:WilsonWindowReportingPace.Slow R.kit)
local notation "a₀" => R.alloy.B.a

include simple slow in
theorem block (d:ℕ) {δ:ℝ} (hp:0<δ):
    ∀ᶠ i:ℕ in atTop,(((a₀).S.block i).val:ℝ)^d ≤ ((a₀).clock.hatBeta (i+1))^δ:=by
  have growth:Tendsto (a₀).clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.family.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have C:0 < (2:ℝ)^d:=by positivity
  have small:= (isLittleO_log_rpow_rpow_atTop (d:ℝ) hp).def (inv_pos.mpr C)
  filter_upwards [growth.eventually small,(tendsto_log_atTop.comp growth).eventually_ge_atTop 1]
    with i bound large
  let b:ℝ:=(a₀).clock.hatBeta i
  have b0:0 ≤ b:=zero_le_one.trans ((a₀).fits.delayed i).le
  have lb:1 ≤ log b:=large
  have lb0:0 ≤ log b:=zero_le_one.trans lb
  have logcost:RG16.Lambda (a₀) i=2+log b:=rfl
  have side:(((a₀).S.block i).val:ℝ) ≤ 2*log b:=by
    have gate:=slow.2 i
    rw [logcost] at gate
    have arg:0<2+log b:=by linarith
    linarith [Real.log_le_sub_one_of_pos arg]
  have estimate:(log b)^d ≤ ((2:ℝ)^d)⁻¹*b^δ:=by
    change ‖(log b)^(d:ℝ)‖ ≤ ((2:ℝ)^d)⁻¹ * ‖b^δ‖ at bound
    simpa only [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg lb0 _),
      abs_of_nonneg (Real.rpow_nonneg b0 δ)] using bound
  calc
    _ ≤ (2*log b)^d:=pow_le_pow_left₀ (Nat.cast_nonneg _) side d
    _ = (2:ℝ)^d*(log b)^d:=mul_pow .. 
    _ ≤ (2:ℝ)^d*(((2:ℝ)^d)⁻¹*b^δ):=mul_le_mul_of_nonneg_left estimate C.le
    _ = b^δ:=by field_simp
    _ ≤ _:=Real.rpow_le_rpow b0 (WilsonStartup.Timing.hat_mono (a₀) (Gauge.slopeConstant_pos simple).le (Nat.le_succ i)) hp.le

include simple slow in
theorem whole (d:ℕ) {δ:ℝ} (hp:0<δ):
    ∀ᶠ i:ℕ in atTop,∀ mass fee:ℝ, 0 ≤ mass →
      fee ≤ (((a₀).S.block i).val:ℝ)^d*(2*((a₀).clock.hatBeta (i+1))^(δ/2))*(1+mass) →
      fee ≤ 2*((a₀).clock.hatBeta (i+1))^δ*(1+mass):=by
  filter_upwards [block R simple slow d (half_pos hp)] with i paid
  intro mass fee hm old
  let b:ℝ:=(a₀).clock.hatBeta (i+1)
  have b0:0 < b:=lt_trans zero_lt_one ((a₀).fits.delayed (i+1))
  have bpos:0 ≤ 2*b^(δ/2):=by positivity
  have square:b^(δ/2)*b^(δ/2)=b^δ:=by rw [←Real.rpow_add b0];congr 1;ring
  calc
    _ ≤ _:=old
    _ ≤ (b^(δ/2)*(2*b^(δ/2)))*(1+mass):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right paid bpos) (by positivity)
    _ = 2*b^δ*(1+mass):=by rw [← square];ring
end YM.Integration.WilsonOlderFreshGraphSlowPreimages
end
