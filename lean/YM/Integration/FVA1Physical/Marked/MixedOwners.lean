import YM.Integration.FVA1Physical.Marked.ShortOwners

/-! Several failed physical source stencils may be assigned to the same
actual vacuum label. The expansion weights sum to one when every source
fails. It uses one copy of the original vacuum product for every assignment. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Finset
open scoped Classical BigOperators

theorem mixed_failed_occurrence {G : Gauge} {c : Side} {M : Type} [Fintype M]
    (P : Rep G c) (S : M → Support c) (F : M → Config G c → ℝ)
    (rows : Finset ℕ) (U : Config G c) :
    P.activities.gasOccurrence P.p rows U * (∏ s, maskFailure P.p (S s) (F s) U) =
      if P.activities.admissible P.p U rows then
        ∑ owner : M → ↥rows, (∏ s, flagShare P (S s) (owner s).val U * F s U) *
          ∏ j ∈ rows, P.activities.K j U else 0 := by
  unfold Activities.gasOccurrence
  by_cases legal : P.activities.admissible P.p U rows
  · simp only [if_pos legal]
    have individual (s : M) : maskFailure P.p (S s) (F s) U =
        ∑ i : ↥rows, flagShare P (S s) i.val U * F s U := by
      rw [← sum_mul, Finset.sum_coe_sort rows (fun i => flagShare P (S s) i U),
        flagShare_partition P (S s) rows U legal]
      unfold maskFailure
      split <;> simp
    simp_rw [individual]
    rw [Fintype.prod_sum (f := fun s (i : ↥rows) => flagShare P (S s) i.val U * F s U), ← sum_mul, mul_comm]
  · simp only [if_neg legal, zero_mul]

end YM.Integration.FVA1Physical.Marked
