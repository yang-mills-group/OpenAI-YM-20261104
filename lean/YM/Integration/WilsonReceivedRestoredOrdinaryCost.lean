import YM.Integration.WilsonReceivedCloseOrdinaryGrade

/-! The physical connected error is paid before summing its ordinary partitions.
Only the full occupied mask pays the inverse of the realized radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedRestoredOrdinaryCost
open Finset Marker Multi Filter
open scoped BigOperators
open private cutoff from YM.Integration.WilsonReceivedCloseOrdinaryGrade
variable {V:Type} [DecidableEq V] [Fintype V] (J:Census V)
def fee (a:ℕ) : ℝ := (Fintype.card (parts J).Mode:ℝ)*((a:ℝ)*4^a+1)
omit [Fintype V] in
theorem nonneg (a:ℕ) : 0≤fee J a := by unfold fee; positivity

omit [Fintype V] in
theorem original (s:J.Mode) (a v q:ℕ) {t τ err E:ℝ}
    (tp:0<t) (cold:t≤1) (live:s.val.card≤a) (wage:t^v≤τ) (en:0≤err) (ep:0≤E)
    (regular:E≤t^(q+1+v+a))
    (actual:τ*err ≤ (∑h∈shards J s,(h.val.card:ℝ)*E*(t⁻¹+E)^h.val.card)
      +t^(q+1+v)*(shards J s).card) :
    err ≤ fee J a*t^(q+1) := by
  let u:=q+1+v
  have inv:t⁻¹≤3*t⁻¹:=by linarith only [(inv_pos.mpr tp).le]
  have sums : (∑h∈shards J s,(h.val.card:ℝ)*E*(t⁻¹+E)^h.val.card) ≤
      ((shards J s).card:ℝ)*(((a:ℝ)*4^a)*t^u) := calc
    _ ≤ ∑_h ∈ shards J s,((a:ℝ)*4^a)*t^u := Finset.sum_le_sum fun h hh=>by
      have power:=pow_le_pow_left₀ (add_nonneg (inv_pos.mpr tp).le ep) (add_le_add (le_refl t⁻¹) regular) h.val.card
      calc
        _ ≤ (h.val.card:ℝ)*t^(u+a)*(t⁻¹+t^(u+a))^h.val.card :=
          mul_le_mul (mul_le_mul_of_nonneg_left regular (Nat.cast_nonneg _)) power (pow_nonneg (by positivity) _) (by positivity)
        _ ≤ _ := cutoff tp cold tp inv a u h.val.card ((WilsonFiniteOrdinaryTail.blocks s h hh).trans live)
    _ = _ := by simp
  have count:((shards J s).card:ℝ)≤Fintype.card (parts J).Mode := Nat.cast_le.mpr (Finset.card_le_univ _)
  have receipt : t^v*err ≤ t^v*(fee J a*t^(q+1)) := calc
    _ ≤ τ*err := mul_le_mul_of_nonneg_right wage en
    _ ≤ _ := actual
    _ ≤ ((shards J s).card:ℝ)*(((a:ℝ)*4^a)*t^u)+t^u*(shards J s).card :=
      add_le_add sums le_rfl
    _ = ((shards J s).card:ℝ)*((a:ℝ)*4^a+1)*t^u := by ring
    _ ≤ (fee J a)*t^u := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right count (by positivity)) (pow_nonneg tp.le _)
    _ = t^v*(fee J a*t^(q+1)) := by dsimp only [u];rw [pow_add];ring
  exact le_of_mul_le_mul_left receipt (pow_pos tp _)

end YM.Integration.WilsonReceivedRestoredOrdinaryCost
