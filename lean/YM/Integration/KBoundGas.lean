import YM.RG.ActivityBounds

/-! The native gas bound uses only the original forced cap. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG.Activities
open Lattice Wilson

variable {G : Gauge} {n : Side} {A : Activities G n}
    {p : BudgetPoint} {w : ℝ}

/-- The whole original gas is uniformly dominated using its KBound alone.
This is the native gasSeries proof with precisely its used hypothesis. -/
theorem gasSeries_of_KBound (H : A.KBound p w) :
    Dominated (A.gasOccurrence p) := by
  obtain ⟨b, hb, h⟩ := K_total H
  refine ⟨fun t => ∏ i ∈ t, b i,
    summable_finsetProd_of_summable_nonneg (fun i => (h i).1) hb, ?_⟩
  intro s U
  unfold gasOccurrence
  split
  · rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (h i).2 U)
  rw [norm_zero]
  exact Finset.prod_nonneg fun i _ => (h i).1

/-- Absolute convergence retains every original finite gas product. -/
theorem gasOccurrence_absolute_of_KBound (H : A.KBound p w)
    (U : Config G n) :
    Summable (fun s : Finset ℕ => ‖A.gasOccurrence p s U‖) :=
  (gasSeries_of_KBound H).absolute U

end YM.RG.Activities
end
