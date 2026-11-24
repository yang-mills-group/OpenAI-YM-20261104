import YM.Integration.FVA1Physical.Marked.WalletSplit
import YM.Corona.Halo

/-! A failed short source is assigned literally to the vacuum rows that own
its failed sites. Overlapping the source on several different owners is
permitted. The fractional allocation commutes with relabeling the sites. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Finset Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {c : Side}

/-- Fraction of a stencil's failed sites covered by a given vacuum inventory. -/
def flagShare (P : Rep G c) (S : Support c) (i : ℕ) (field : Config G c) : ℝ :=
  let X := S ∩ flags P.p.threshold field
  ∑ y ∈ X, if y ∈ (P.activities.forced i).inventory then (X.card : ℝ)⁻¹ else 0

theorem flagShare_nonneg (P : Rep G c) (S : Support c) (i : ℕ) (U : Config G c) :
    0 ≤ flagShare P S i U := by
  unfold flagShare
  apply sum_nonneg
  intro y _
  split <;> positivity

theorem flagShare_le_one (P : Rep G c) (S : Support c) (i : ℕ) (U : Config G c) :
    flagShare P S i U ≤ 1 := by
  let X := S ∩ flags P.p.threshold U
  change (∑ y ∈ X, if y ∈ _ then (X.card : ℝ)⁻¹ else 0) ≤ 1
  calc
    _ ≤ ∑ _ ∈ X, (X.card : ℝ)⁻¹ := sum_le_sum (fun y _ => by split <;> first | exact le_rfl | positivity)
    _ ≤ 1 := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_inv_le_one

theorem flagShare_support (P : Rep G c) (S : Support c) (i : ℕ)
    (h : Disjoint S (P.activities.forced i).inventory) (U : Config G c) :
    flagShare P S i U = 0 := by
  unfold flagShare
  exact sum_eq_zero fun y hy => if_neg (Finset.disjoint_left.mp h (mem_inter.mp hy).1)

/-- Admissibility of the actual gas occurrence partitions the failed sites.
No geometric width assumption on its forced rows is required. -/
theorem flagShare_partition (P : Rep G c) (S : Support c) (rows : Finset ℕ)
    (U : Config G c) (h : P.activities.admissible P.p U rows) :
    ∑ i ∈ rows, flagShare P S i U = if Healthy P.p.threshold S U then 0 else 1 := by
  let X := S ∩ flags P.p.threshold U
  unfold flagShare
  rw [sum_comm]
  by_cases good : Healthy P.p.threshold S U
  · have he : X = ∅ := Finset.disjoint_iff_inter_eq_empty.mp good
    rw [if_pos good]
    change (∑ _ ∈ X, _) = 0
    rw [he, sum_empty]
  · have hX : X.Nonempty := by
      obtain ⟨y,hy,hy'⟩ := Finset.not_disjoint_iff.mp good
      exact ⟨y,mem_inter.mpr ⟨hy,hy'⟩⟩
    have unique (y) (hy : y ∈ X) : ∃ i ∈ rows, y ∈ (P.activities.forced i).inventory ∧
        ∀ j ∈ rows, y ∈ (P.activities.forced j).inventory → j = i := by
      obtain ⟨i,hi,hy'⟩ := mem_biUnion.mp (h.2.symm ▸ (mem_inter.mp hy).2)
      refine ⟨i,hi,hy',?_⟩
      intro j hj hj'
      by_contra ne
      exact disjoint_left.mp (h.1 hj hi ne) ((P.activities.forced j).inventory_sup hj')
        ((P.activities.forced i).inventory_sup hy')
    rw [if_neg good]
    change (∑ y ∈ X, ∑ i ∈ rows, if y ∈ (P.activities.forced i).inventory then (X.card : ℝ)⁻¹ else 0) = 1
    calc
      _ = ∑ _ ∈ X, (X.card : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro y hy
        obtain ⟨i,hi,hy',only⟩ := unique y hy
        rw [sum_eq_single_of_mem i hi (fun j hj ne => if_neg (fun hz => ne (only j hj hz))), if_pos hy']
      _ = 1 := by
        rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hX.card_pos.ne')]

/-- Multiply the failed source by its actual vacuum host, preserving the
entire unmodified product on the other rows, even when some amplitudes vanish. -/
theorem failed_occurrence (P : Rep G c) (S : Support c) (F : Config G c → ℝ)
    (rows : Finset ℕ) (U : Config G c) :
    P.activities.gasOccurrence P.p rows U * maskFailure P.p S F U =
      if P.activities.admissible P.p U rows then
        ∑ i ∈ rows, (flagShare P S i U * P.activities.K i U * F U) *
          ∏ j ∈ rows.erase i, P.activities.K j U else 0 := by
  unfold Activities.gasOccurrence maskFailure
  by_cases hr : P.activities.admissible P.p U rows
  · simp only [if_pos hr]
    have h := flagShare_partition P S rows U hr
    rw [show (∑ i ∈ rows, (flagShare P S i U * P.activities.K i U * F U) *
          ∏ j ∈ rows.erase i, P.activities.K j U) =
        (∑ i ∈ rows, flagShare P S i U) * (∏ j ∈ rows, P.activities.K j U) * F U by
      rw [sum_mul, sum_mul]
      apply sum_congr rfl
      intro i hi
      rw [← rows.mul_prod_erase (fun k => P.activities.K k U) hi]
      ring, h]
    split <;> ring
  · simp only [if_neg hr, zero_mul]

end YM.Integration.FVA1Physical.Marked
