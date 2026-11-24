import YM.Integration.WilsonOriginalNullClock
import YM.Integration.WilsonOlderFreshGraphSlowPreimages

/-! A positive share of the original null rate pays the restored hard row.
This uses the enrolled block size and the actual near-top coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullScale
open Function Filter Finset Lattice Wilson RG Source Labels PhysicalNext PhysicalNext.Repeat
open Legato Peak Org JointLoad Clockwork LocalComparison Next.Foundations Push.Local
open Graces Extra.Histories Push.PriceCompiler
open scoped BigOperators Topology Classical
variable {G : Gauge}

theorem regular (P : Stage) (d : ℕ) (L : Side) :
    6 * vigors G P d * coinFee G P d L ≤ Doors.rate L := by
  let v := vigors G P d
  let b := Motion.orbitCost ((Labels.frames G).level d)
  have hb : 1 ≤ b := Motion.orbitCost_one_le _
  have base : 1 ≤ (2:ℝ)*2^P.power := by
    have : 1 ≤ (2:ℝ)^P.power := one_le_pow₀ (by norm_num)
    linarith
  have hf : 1 ≤ faded P := one_le_pow₀ base
  have h1 := mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hb)
  have h2 := mul_nonneg (abs_nonneg v) (sub_nonneg.mpr (hf.trans (le_abs_self _)))
  have bound : 6*v ≤ host G P d := by
    change 6*v ≤ 1 + 2 * |v| * (1 + b + |faded P|)
    linarith [le_abs_self v]
  calc
    _ ≤ host G P d * coinFee G P d L := mul_le_mul_of_nonneg_right bound (coin_pos G P d L).le
    _ = _ := by unfold coinFee; field_simp [(simpleH G P d).ne']

variable (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
local notation "a₀" => R.alloy.B.a
include simple slow in
theorem forced (d : ℕ) : ∀ᶠ i : ℕ in atTop,
    let L := R.rolls.L ((a₀).clock.J (i+1))
    3 * ((L.val:ℝ)^d * (a₀).clock.hatBeta (i+1)^(-(1:ℝ))) ≤ Doors.rate L := by
  filter_upwards [WilsonOlderFreshGraphSlowPreimages.block R simple slow (d+2) (show 0 < (1:ℝ) by norm_num)] with i cost
  rw [Real.rpow_one,block_eq R.alloy.B.valid i] at cost
  let L := R.rolls.L ((a₀).clock.J (i+1))
  let l : ℝ := L.val
  let x := (a₀).clock.hatBeta (i+1)
  have large : (3:ℕ) ≤ L.val := by
    change 3 ≤ (R.rolls.L ((a₀).clock.J (i+1))).val
    rw [← block_eq R.alloy.B.valid]
    exact (a₀).S.block_large i
  have hlarge : 3 ≤ l := by
    change (3:ℝ) ≤ (L.val:ℝ)
    exact_mod_cast large
  have pos : 0 < l := by linarith
  have beta : 0 < x := (lt_trans (by norm_num) ((a₀).fits.delayed (i+1)))
  have bill : 3*(l^d*x⁻¹) ≤ l⁻¹ := by
    calc
      _ = (3*l^d)/x := by ring
      _ ≤ l⁻¹ := by
        apply (div_le_iff₀ beta).2
        rw [←div_eq_inv_mul]
        apply (le_div_iff₀ pos).2
        calc
          _ ≤ l*l^d*l := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlarge (pow_nonneg pos.le _)) pos.le
          _ = l^(d+2) := by ring
          _ ≤ x := cost
  change 3*(l^d*x^(-(1:ℝ))) ≤ l^(-(2/5:ℝ))
  rw [Real.rpow_neg_one]
  exact bill.trans (by rw [← Real.rpow_neg_one]; apply Real.rpow_le_rpow_of_exponent_le (by linarith); norm_num)

end YM.Integration.WilsonOriginalNullScale
