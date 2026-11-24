import YM.Integration.WilsonPhysicalHistoryRootVolume

/-! For a fixed finite census the per-name divided bills can buy the original
all-hit hard hypothesis directly. The quiet coefficient stays with its own
vacuum bill on the same original addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFiniteTicket
open Finset Lattice Wilson RG Marker Extra.Multi
open scoped Classical BigOperators

variable {V I : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side}
  (C : Census V) (D : I → ForcedAddress G n) (majorant : I → Poly C)
  (weights : V → ℝ) (positive : ∀ v, 0 < weights v) {B : ℕ} {A quiet marked : ℝ}

private theorem named {K : Type*} {members : K → Finset V} {support : K → Support n}
    {fee : K → ℝ} (nonneg : ∀ i, 0 ≤ fee i) (active : ∀ i, 0 < fee i → (members i).Nonempty)
    (income : Rooted members support B A fee marked) :
    SumBudget (fun i => Real.exp (A * coverNumber B (support i)) * fee i)
      ((Fintype.card V : ℝ) * marked) := by
  classical
  let per (v : V) (i : K) :=
    if v ∈ members i then Real.exp (A * coverNumber B (support i)) * fee i else 0
  have per_paid (v : V) : SumBudget (per v) marked := by
    convert income v using 1
    funext i
    by_cases included : v ∈ members i <;> simp [per, included]
  apply Budget.certify (fun i => mul_nonneg (Real.exp_pos _).le (nonneg i))
  intro entries
  calc
    _ ≤ ∑ i ∈ entries, ∑ v, per v i := by
      apply sum_le_sum
      intro i _
      by_cases h : 0 < fee i
      · obtain ⟨v, hv⟩ := active i h
        have booked : per v i = _ := if_pos hv
        rw [← booked]
        exact single_le_sum (fun j _ => (per_paid j).1 i) (mem_univ v)
      · rw [le_antisymm (le_of_not_gt h) (nonneg i), mul_zero]
        exact sum_nonneg fun v _ => (per_paid v).1 i
    _ = ∑ v, ∑ i ∈ entries, per v i := sum_comm
    _ ≤ ∑ _v : V, marked := sum_le_sum fun v _ => Budget.cap (per_paid v) entries
    _ = _ := by simp

include positive in
theorem paid
    (bare : Ac.Hit (fun i => (D i).support) B
      (fun i => Poly.toll weights C.quiet * ‖(majorant i).part C.quiet‖) A quiet)
    (divided : Rooted (fun j : I × C.Mode => j.2.val) (fun j => (D j.1).support) B A
      (fun j => Poly.toll weights j.2 * ‖(majorant j.1).part j.2‖) marked) :
    Ac.Hit (fun i => (D i).support) B (fun i => Poly.price weights (majorant i)) A
      (quiet + (Fintype.card V : ℝ) * marked) := by
  classical
  let part (i : I × C.Mode) := Poly.toll weights i.2 * ‖(majorant i.1).part i.2‖
  let rest (i : I × C.Mode) := if i.2 = C.quiet then 0 else part i
  have money (i : I × C.Mode) : 0 ≤ part i :=
    mul_nonneg (Poly.worth positive _).le (norm_nonneg _)
  have nonneg (i : I × C.Mode) : 0 ≤ rest i := by
    dsimp only [rest]
    split
    · exact le_rfl
    · exact money i
  have active (i : I × C.Mode) (h : 0 < rest i) : i.2.val.Nonempty := by
    refine Finset.nonempty_iff_ne_empty.mpr fun empty => ?_
    have he : i.2 = C.quiet := Subtype.ext empty
    simp [rest,he] at h
  have bank : Rooted (fun j : I × C.Mode => j.2.val) (fun j => (D j.1).support)
      B A rest marked := by
    apply Rooted.mono divided nonneg _ le_rfl le_rfl
    intro i
    dsimp only [rest]
    split
    · exact money i
    · exact le_rfl
  have all := named nonneg active bank
  have colored := WilsonPhysicalHistoryRootVolume.tabulate D rest nonneg all
  have recombine (i : I) : part (i,C.quiet) + ∑ s, rest (i,s) = Poly.price weights (majorant i) := by
    have separate : (∑ s : C.Mode, if s = C.quiet then part (i,C.quiet) else 0)
        = part (i,C.quiet) := by simp
    rw [← separate, ← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    by_cases closed : s = C.quiet
    · subst s
      simp [rest, part]
    · simp [rest, closed, part]
  intro x
  convert Budget.plus (bare x) (colored x) using 1
  funext i
  by_cases hx : x ∈ (D i).support
  · simp only [if_pos hx, ← add_mul, ← recombine i]
    rfl
  · simp [hx]

end YM.Integration.WilsonPhysicalHistoryFiniteTicket
end

