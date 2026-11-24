import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Embedding.Basic

/-! Restrict finite coordinate sums through an actual injection of alphabets.
The original weight is evaluated after the coordinate map. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FiniteCoordinateRestriction

open scoped BigOperators Classical

universe u v w
variable {F : Type u} {I : Type v} {J : Type w}
    [Fintype F] [Fintype I] [Fintype J]

/-- Restricting every coordinate cannot increase a nonnegative finite sum.
The slot set may be empty. -/
theorem whole_sum_le (e : I ↪ J) (W : (F → J) → ℝ)
    (hW : ∀ y, 0 ≤ W y) :
    (∑ x : F → I, W (e ∘ x)) ≤ ∑ y : F → J, W y := by
  let f : (F → I) ↪ (F → J) := Function.Embedding.arrowCongrRight e
  calc
    _ = ∑ y ∈ Finset.univ.map f, W y :=
      (Finset.sum_map Finset.univ f W).symm
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg hW

/-- The same restriction preserves an actual fixed coordinate and its value. -/
theorem fixed_port_sum_le (e : I ↪ J) (W : (F → J) → ℝ)
    (hW : ∀ y, 0 ≤ W y) (p : F) (i0 : I) :
    (∑ x : F → I, if x p = i0 then W (e ∘ x) else 0) ≤
      ∑ y : F → J, if y p = e i0 then W y else 0 := by
  have hn (y : F → J) :
      0 ≤ (if y p = e i0 then W y else 0) := by
    by_cases hy : y p = e i0
    · simpa only [if_pos hy] using hW y
    · simp only [if_neg hy, le_refl]
  have h := whole_sum_le e (fun y => if y p = e i0 then W y else 0) hn
  simpa only [Function.comp_apply, e.injective.eq_iff] using h

end YM.Integration.FiniteCoordinateRestriction
end
