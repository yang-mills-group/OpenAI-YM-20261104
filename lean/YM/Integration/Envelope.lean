import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option autoImplicit false
noncomputable section
namespace YM.Integration

/-- Including zero avoids an inhabitedness assumption on the probe domain. -/
def envelope {α : Type*} (f : α → ℝ) : ℝ := sSup (insert 0 (Set.range f))

lemma envelope_le {α : Type*} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, f x ≤ C) : envelope f ≤ C := by
  apply csSup_le (Set.insert_nonempty 0 _)
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | ⟨x, rfl⟩
  · exact hC
  · exact hf x

lemma envelope_bdd {α : Type*} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, f x ≤ C) : BddAbove (insert 0 (Set.range f)) := by
  refine ⟨C, ?_⟩
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | ⟨x, rfl⟩
  · exact hC
  · exact hf x

lemma envelope_nonneg {α : Type*} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, f x ≤ C) : 0 ≤ envelope f :=
  le_csSup (envelope_bdd hC hf) (Set.mem_insert 0 _)

lemma le_envelope {α : Type*} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, f x ≤ C) (x : α) : f x ≤ envelope f :=
  le_csSup (envelope_bdd hC hf) (Set.mem_insert_of_mem 0 (Set.mem_range_self x))

end YM.Integration
