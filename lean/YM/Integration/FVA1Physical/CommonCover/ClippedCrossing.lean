import Mathlib

/-! A restored signed reading has a gross cap. Using that cap before testing
the relative two-source invoice reduces the third inverse gas power to one
inverse gas in its squared cost. The latter cancels against a gas-weighted
physical marginal on the same event. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Crossing
open MeasureTheory

/-- The two singleton inputs are the norms of the raw, unnormalized marked
rows in their original weights. -/
def invoice (ν W M a b : ℝ) : ℝ :=
  2*W*(M+(1+a/ν)*(1+b/ν))/ν

theorem clipped_square {ν W M a b κ : ℝ}
    (gas : 0 < ν) (unit : ν ≤ 1) (cross : 0 ≤ W) (gross : 0 ≤ M)
    (ap : 0 ≤ a) (bp : 0 ≤ b) (ha : a ≤ κ) (hb : b ≤ κ) :
    (min M (invoice ν W M a b))^2 * ν ≤
      (M^5 * (2*W*(M+(1+κ)^2))) ^ ((3 : ℝ)⁻¹) := by
  let v := min M (invoice ν W M a b)
  have kpos := ap.trans ha
  have vp : 0 ≤ v := le_min gross (by unfold invoice; positivity)
  have cube : invoice ν W M a b * ν^3 =
      2*W*(M*ν^2+(ν+a)*(ν+b)) := by
    dsimp only [invoice]
    field_simp [gas.ne']
  have sumBound : M*ν^2+(ν+a)*(ν+b) ≤ M+(1+κ)^2 := by
    apply add_le_add
    · exact mul_le_of_le_one_right gross (pow_le_one₀ gas.le unit)
    · rw [sq]
      exact mul_le_mul (add_le_add unit ha) (add_le_add unit hb) (add_nonneg gas.le bp)
        (add_nonneg zero_le_one kpos)
  have t : v*ν^3 ≤ 2*W*(M+(1+κ)^2) :=
    ((mul_le_mul_of_nonneg_right (min_le_right ..) (pow_nonneg gas.le _)).trans_eq cube).trans
      (mul_le_mul_of_nonneg_left sumBound (mul_nonneg zero_le_two cross))
  apply (pow_le_pow_iff_left₀ (mul_nonneg (sq_nonneg _) gas.le)
    (Real.rpow_nonneg (by positivity) _) (by decide : 3 ≠ 0)).mp
  have root : ((M^5 * (2*W*(M+(1+κ)^2))) ^ ((3:ℝ)⁻¹)) ^ (3:ℕ) =
      M^5 * (2*W*(M+(1+κ)^2)) := by
    simpa using Real.rpow_inv_natCast_pow (x:=M^5 * (2*W*(M+(1+κ)^2)))
      (by positivity) (by decide : (3:ℕ) ≠ 0)
  rw [root]
  change (v^2*ν)^3 ≤ _
  calc
    (v^2*ν)^3 = v^5*(v*ν^3) := by ring
    _ ≤ M^5*(2*W*(M+(1+κ)^2)) :=
      mul_le_mul (pow_le_pow_left₀ vp (min_le_left ..) _) t
        (mul_nonneg vp (pow_nonneg gas.le _)) (pow_nonneg gross _)

/-- An upper bound on the whole restored error and the separate comparison
bound are sufficient to truncate the unpaid term pointwise. -/
theorem clip_error {d r M c : ℝ} (gross : d ≤ M) (regular : 0 ≤ r) (split : d ≤ r+c) :
    d ≤ r+min M c := by
  rw [add_min]
  exact le_min (gross.trans (le_add_of_nonneg_left regular)) split

end YM.Integration.FVA1Physical.Crossing
