import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic

/-! Freeze every coupling coordinate at None and embed every remaining field
coordinate through Some, retaining the original ordered slot equivalence. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FixedNoneCoordinateRestriction

open scoped BigOperators Classical

universe u v w
variable {C : Type u} {F : Type v} {I : Type w} {n : ℕ}

/-- The original ordered table assignment with all coupling slots fixed. -/
def fill (e : Fin n ≃ C ⊕ F) (x : F → I) (k : Fin n) : Option I :=
  Sum.elim (fun _ => none) (fun f => some (x f)) (e k)

private def fillEmbedding (e : Fin n ≃ C ⊕ F) :
    (F → I) ↪ (Fin n → Option I) where
  toFun := fill e
  inj' := by
    intro x y hxy
    funext f
    simpa [fill] using congrFun hxy (e.symm (Sum.inr f))

variable [Fintype F] [Fintype I]

/-- Freezing coupling slots and restricting field labels does not increase the
same anchored marginal. The fixed field port is supplied explicitly. -/
theorem fixed_field_marginal (e : Fin n ≃ C ⊕ F)
    (T : (Fin n → Option I) → ℂ) (p : F) (i0 : I) {A : ℝ}
    (hT : (∑ y : Fin n → Option I,
      if y (e.symm (Sum.inr p)) = some i0 then ‖T y‖ else 0) ≤ A) :
    (∑ x : F → I, if x p = i0 then ‖T (fill e x)‖ else 0) ≤ A := by
  let W : (Fin n → Option I) → ℝ := fun y =>
    if y (e.symm (Sum.inr p)) = some i0 then ‖T y‖ else 0
  have hW (y : Fin n → Option I) : 0 ≤ W y := by
    by_cases hy : y (e.symm (Sum.inr p)) = some i0
    · simpa only [W, if_pos hy] using norm_nonneg (T y)
    · simp only [W, if_neg hy, le_refl]
  have hs : (∑ x : F → I, W (fill e x)) ≤ ∑ y : Fin n → Option I, W y := by
    calc
      _ = ∑ y ∈ Finset.univ.map (fillEmbedding e), W y :=
        (Finset.sum_map Finset.univ (fillEmbedding e) W).symm
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg hW
  simpa [W, fill] using hs.trans hT

end YM.Integration.FixedNoneCoordinateRestriction
end
