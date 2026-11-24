import YM.Integration.WilsonOriginalNullFamily
import YM.Trace.Physicalv2.GermPrices

/-! Pay the native lower section size against the one-date null contraction
on the original physical calendar, also when that calendar changes stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullStock
open Function Filter Lattice Wilson RG Source Labels Trace.Physical.GermGraph Real
open scoped Classical Topology BigOperators
variable {G : Gauge} (C : Family G)

theorem adjacent (i : ℕ) : factor C i ≤ factor C (i+1) := by
  let A := C.path.levels
  have mono := A.fits.monotoneL (A.fits.mono (Nat.le_succ (i+1)))
  change (A.clock.factor (A.clock.J (i+1))).val ≤ (A.clock.factor (A.clock.J (i+1+1))).val at mono
  rw [A.fits.sameFactor i,A.fits.sameFactor (i+1)] at mono
  change ((A.S.block i).val:ℝ) ≤ ((A.S.block (i+1)).val:ℝ)
  exact_mod_cast mono

theorem original : ∀ᶠ i : ℕ in atTop,
    4*(2+4*(C.path.levels.params i).columns)*(factor C i)^(-(2/5:ℝ)) ≤
      (factor C i)^(-(1/8:ℝ)) := by
  obtain ⟨base,previous⟩ := eventually_atTop.1 (factor_large C (1/16) (by norm_num))
  have rising : Tendsto (factor C) atTop atTop := tendsto_atTop.2 fun a => by
    let b := max 1 a
    have hb : 0 < b := zero_lt_one.trans_le (le_max_left _ _)
    filter_upwards [factor_large C b⁻¹ (inv_pos.mpr hb)] with j his
    exact (le_max_right _ _).trans (inv_inv b ▸ his.1)
  have grown : Tendsto (fun i => (factor C i)^(1/8:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < (1/8:ℝ) by norm_num)).comp rising
  filter_upwards [eventually_ge_atTop (base+1),grown.eventually_ge_atTop 12] with i late high
  cases i with
  | zero => omega
  | succ j =>
    let l := factor C (j+1)
    have old := (previous j (Nat.le_of_succ_le_succ late)).2
    have leone : (1:ℝ) ≤ l := le_of_lt (factor_positive C _)
    have pos := lt_of_lt_of_le zero_lt_one leone
    have single : 4*stock C (j+1) ≤ l^(1/16:ℝ) := old.trans
      (Real.rpow_le_rpow (zero_lt_one.trans (factor_positive C j)).le (adjacent C j) (by norm_num))
    have one : (1:ℝ) ≤ l^(1/16:ℝ) := Real.one_le_rpow leone (by norm_num)
    have head : 4*(2+4*stock C (j+1)) ≤ 12*l^(1/16:ℝ) := by linarith only [single,one]
    have joint : 4*(2+4*stock C (j+1)) ≤ l^((1/8:ℝ)+1/16) := by
      rw [rpow_add pos]
      exact head.trans (mul_le_mul_of_nonneg_right high (one.trans' zero_le_one))
    calc
      _ ≤ l^((1/8:ℝ)+1/16)*l^(-(2/5:ℝ)) :=
        mul_le_mul_of_nonneg_right joint (rpow_nonneg pos.le _)
      _ = l^((1/8:ℝ)+1/16 + -(2/5:ℝ)) := (rpow_add pos _ _).symm
      _ ≤ l^(-(1/8:ℝ)) := Real.rpow_le_rpow_of_exponent_le leone (by norm_num)

end YM.Integration.WilsonOriginalNullStock
