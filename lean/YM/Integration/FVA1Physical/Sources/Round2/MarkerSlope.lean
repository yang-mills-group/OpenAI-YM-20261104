import YM.Marker.Truncated

/-! The Lipschitz cost of a marker exponential in the unit-weight price.
The coefficient of the linear error remains explicit at all cutoffs. -/

namespace YM.Integration.FVA1Physical.Round2

open Marker
open scoped BigOperators

noncomputable def markerSlope (K : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (K + 1)).erase 0, ‖((k.factorial : ℂ)⁻¹)‖ * t ^ (k - 1)

theorem price_pass_sub_one {I : Type} [DecidableEq I] [Fintype I] {B : Census I}
    (X : Poly B) {t : ℝ} (hX : Poly.price (fun _ => 1) X ≤ t) :
    Poly.price (fun _ => 1) (Poly.pass X - 1) ≤ markerSlope (Fintype.card I) t * t := by
  let s := Finset.range (Fintype.card I + 1)
  let f := fun k : ℕ => ((k.factorial : ℂ)⁻¹) • X ^ k
  have hpass : Poly.pass X - 1 = ∑ k ∈ s.erase 0, f k := by
    unfold Poly.pass
    rw [← Finset.sum_erase_add s _ (Finset.mem_range.mpr (Nat.zero_lt_succ _))]
    simp [f]
  rw [hpass]
  apply (Poly.batch (fun _ => zero_lt_one) _ f).trans
  unfold markerSlope
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Finset.mem_erase.mp hk).1)
  unfold f
  rw [Poly.adapted, mul_assoc, ← pow_succ, hk']
  exact mul_le_mul_of_nonneg_left ((Poly.powers (fun _ => zero_lt_one) X k).trans
    (pow_le_pow_left₀ (Poly.nonnegative (fun _ => zero_lt_one) X) hX k)) (norm_nonneg _)

end YM.Integration.FVA1Physical.Round2
