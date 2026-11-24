import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Signed ordered cofactors retain the exact remaining inventory and the
compatibility with the distinguished original row. No positivity is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CoveredSignedCofactors
open Finset SectorNext.Vacuum
open scoped Classical BigOperators
variable {J A : Type*} [CommRing A]

/-- Conditions on the original rows left after deleting one address. -/
def Pinned (K Z : ℕ → Finset J) (D : Finset J) (i : ℕ) (t : Finset ℕ) : Prop :=
  i ∉ t ∧ Z i ⊆ D ∧ (∀ j ∈ t, Disjoint (K i) (K j)) ∧
    accounted K Z (D \ Z i) t

/-- Smaller addresses use the retained row, larger addresses the full row. -/
def mixed (F G : ℕ → A) (i : ℕ) (s : Finset ℕ) : A :=
  ∏ j ∈ s.erase i, if j < i then G j else F j

/-- The original packet index is kept; its remaining rows cover D minus Z i. -/
def cofactorTerm (K Z : ℕ → Finset J) (D : Finset J)
    (F G : ℕ → A) (i : ℕ) (s : Finset ℕ) : A :=
  if i ∈ s ∧ Pinned K Z D i (s.erase i) then mixed F G i s else 0

theorem pinned_erase (K Z : ℕ → Finset J) (hZ : ∀ i, Z i ⊆ K i)
    (D : Finset J) (s : Finset ℕ) (h : accounted K Z D s)
    (i : ℕ) (hi : i ∈ s) : Pinned K Z D i (s.erase i) := by
  have hr := reaccounts K Z h hZ i hi
  have he : (fun a b : ℕ => Classical.propDecidable (a = b)) =
      instDecidableEqNat := Subsingleton.elim _ _
  rw [he] at hr
  refine ⟨notMem_erase i s, minus K Z h hZ i hi, ?_, hr⟩
  intro j hj
  exact h.1 hi (mem_of_mem_erase hj) (Ne.symm (mem_erase.mp hj).1)

theorem pinned_insert (K Z : ℕ → Finset J) (D : Finset J)
    (i : ℕ) (t : Finset ℕ) (h : Pinned K Z D i t) :
    accounted K Z D (insert i t) := by
  rcases h with ⟨_hi, hZ, hd, ht⟩
  constructor
  · intro a ha b hb hab
    change a ∈ insert i t at ha
    change b ∈ insert i t at hb
    rcases mem_insert.mp ha with hai | hat
    · subst a
      rcases mem_insert.mp hb with hbi | hbt
      · exact (hab hbi.symm).elim
      · exact hd b hbt
    · rcases mem_insert.mp hb with hbi | hbt
      · subst b
        exact (hd a hat).symm
      · exact ht.1 hat hbt hab
  · rw [biUnion_insert, ht.2]
    exact union_sdiff_of_subset hZ

theorem pinned_erase_iff (K Z : ℕ → Finset J) (hZ : ∀ i, Z i ⊆ K i)
    (D : Finset J) (i : ℕ) (s : Finset ℕ) :
    (i ∈ s ∧ Pinned K Z D i (s.erase i)) ↔ (accounted K Z D s ∧ i ∈ s) := by
  constructor
  · rintro ⟨hi, hp⟩
    refine ⟨?_, hi⟩
    simpa only [insert_erase hi] using pinned_insert K Z D i (s.erase i) hp
  · rintro ⟨h, hi⟩
    exact ⟨hi, pinned_erase K Z hZ D s h i hi⟩

theorem mixed_eq (F G : ℕ → A) (i : ℕ) (s : Finset ℕ) :
    mixed F G i s =
      (∏ j ∈ s with j < i, G j) * ∏ j ∈ s with i < j, F j := by
  have hl : (s.erase i).filter (fun j => j < i) = s.filter (fun j => j < i) := by
    ext j
    constructor
    · intro hj
      exact mem_filter.mpr ⟨mem_of_mem_erase (mem_filter.mp hj).1, (mem_filter.mp hj).2⟩
    · intro hj
      have h := mem_filter.mp hj
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨ne_of_lt h.2, h.1⟩, h.2⟩
  have hr : (s.erase i).filter (fun j => ¬j < i) = s.filter (fun j => i < j) := by
    ext j
    constructor
    · intro hj
      have h := mem_filter.mp hj
      have hm := mem_erase.mp h.1
      exact mem_filter.mpr ⟨hm.2, by omega⟩
    · intro hj
      have h := mem_filter.mp hj
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨ne_of_gt h.2, h.1⟩, by omega⟩
  unfold mixed
  rw [prod_ite, hl, hr]

theorem product_difference (F G : ℕ → A) (s : Finset ℕ) :
    (∏ i ∈ s, F i) - ∏ i ∈ s, G i =
      ∑ i ∈ s, (F i - G i) * mixed F G i s := by
  have h : (∏ i ∈ s, G i) = (∏ i ∈ s, F i) -
      ∑ i ∈ s, (F i - G i) * mixed F G i s := by
    simpa only [sub_sub_cancel, mixed_eq, mul_assoc] using
      prod_sub_ordered s F (fun i => F i - G i)
  rw [h]
  ring

theorem packet_difference (K Z : ℕ → Finset J) (hZ : ∀ i, Z i ⊆ K i)
    (D : Finset J) (F G : ℕ → A) (s : Finset ℕ) :
    (if accounted K Z D s then (∏ i ∈ s, F i) - ∏ i ∈ s, G i else 0) =
      ∑ i ∈ s, (F i - G i) * cofactorTerm K Z D F G i s := by
  by_cases h : accounted K Z D s
  · rw [if_pos h, product_difference]
    apply sum_congr rfl
    intro i hi
    unfold cofactorTerm
    rw [if_pos ⟨hi, pinned_erase K Z hZ D s h i hi⟩]
  · rw [if_neg h]
    symm
    apply sum_eq_zero
    intro i hi
    have hn : ¬ (i ∈ s ∧ Pinned K Z D i (s.erase i)) :=
      fun hp => h ((pinned_erase_iff K Z hZ D i s).mp hp).1
    simp only [cofactorTerm, if_neg hn, mul_zero]

end YM.Integration.CoveredSignedCofactors
