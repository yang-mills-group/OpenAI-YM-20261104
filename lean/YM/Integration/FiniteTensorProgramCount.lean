import YM.Comparison.RG02.Sky.Rig

/-!
# Finite size of the literal connected pairing program

The estimate counts the original ordered list, including every repeated entry.
It uses only the number of leg occurrences. No site or colour alphabet, tensor,
covariance, period, or geometric scale enters the bound.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FiniteTensorProgramCount

open Finset
open YM.Comparison.RG02.Cumulants
open YM.Comparison.RG02.Sky
open scoped Classical

private lemma flatMap_length_le {α β : Type*} (l : List α)
    (f : α → List β) (M : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ M) :
    (l.flatMap f).length ≤ l.length * M := by
  revert h
  induction l with
  | nil =>
    intro _
    simp
  | cons x xs ih =>
    intro h
    have hx : (f x).length ≤ M := h x (by simp)
    have hs : (xs.flatMap f).length ≤ xs.length * M :=
      ih (fun y hy => h y (by simp [hy]))
    calc
      ((x :: xs).flatMap f).length =
          (f x).length + (xs.flatMap f).length := by simp
      _ ≤ M + xs.length * M := Nat.add_le_add hx hs
      _ = (x :: xs).length * M := by
        rw [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

section Circle

variable {I A : Type*} [DecidableEq I] [DecidableEq A] [Fintype A]
variable (π : I → A)

private lemma circle_length_aux (B : ℕ) :
    ∀ (N : ℕ) (p : Finset I) (S : Finset A), p.card ≤ B →
      (Traces.circle π p S N).length ≤ (B + 1) ^ N := by
  intro N
  induction N with
  | zero =>
    intro p S _
    rw [Traces.circle]
    split_ifs <;> simp
  | succ N ih =>
    intro p S hp
    rw [Traces.circle]
    split_ifs with h hS
    · let i := Classical.choose h
      let t := Wick.legs π (p.erase i) (univ : Finset A)
      let continuations (j : I) : List (Traces.Path I) :=
        (Traces.circle π ((p.erase i).erase j) (insert (π j) S) N).map
          (fun w => (i, j) :: w)
      have ht : t.card ≤ B := by
        calc
          t.card ≤ (p.erase i).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ p.card := Finset.card_erase_le
          _ ≤ B := hp
      have hc (j : I) : (continuations j).length ≤ (B + 1) ^ N := by
        simpa only [continuations, List.length_map] using
          ih ((p.erase i).erase j) (insert (π j) S)
            (Finset.card_erase_le.trans (Finset.card_erase_le.trans hp))
      change (t.toList.flatMap continuations).length ≤ (B + 1) ^ (N + 1)
      calc
        (t.toList.flatMap continuations).length ≤
            t.toList.length * (B + 1) ^ N :=
          flatMap_length_le _ _ _ (fun j _ => hc j)
        _ = t.card * (B + 1) ^ N := by rw [Finset.length_toList]
        _ ≤ B * (B + 1) ^ N := Nat.mul_le_mul_right _ ht
        _ ≤ (B + 1) * (B + 1) ^ N :=
          Nat.mul_le_mul_right _ (Nat.le_succ B)
        _ = (B + 1) ^ (N + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    · exact Nat.one_le_pow (N + 1) (B + 1) (Nat.succ_pos B)
    · exact Nat.zero_le _

/-- The deterministic first leg leaves at most `p.card` choices at each
recursive step. The terminal singleton, when present, is counted. -/
theorem circle_length_le (p : Finset I) (S : Finset A) (N : ℕ) :
    (Traces.circle π p S N).length ≤ (p.card + 1) ^ N :=
  circle_length_aux π p.card N p S le_rfl

/-- Every original list entry has at most one new edge per recursive step. -/
theorem circle_record_length_le (N : ℕ) :
    ∀ (p : Finset I) (S : Finset A) (f : Traces.Path I),
      f ∈ Traces.circle π p S N → f.length ≤ N := by
  induction N with
  | zero =>
    intro p S f hf
    rw [Traces.circle] at hf
    split_ifs at hf <;> simp_all
  | succ N ih =>
    intro p S f hf
    rw [Traces.circle] at hf
    split_ifs at hf with h hS
    · simp only [List.mem_flatMap, List.mem_map] at hf
      obtain ⟨j, _, w, hw, rfl⟩ := hf
      exact Nat.succ_le_succ (ih _ _ _ hw)
    · simp_all
    · simp_all

end Circle

section Program

variable {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Type) [∀ v, Fintype (U v)] [∀ v, DecidableEq (U v)]

/-- A bound before any site alphabet or period is chosen. Every occurrence
of the native `Rig.program` list is retained. -/
theorem program_length_le (root : V) :
    (Rig.program U root).length ≤
      (Fintype.card (Sigma U) + 1) ^ Fintype.card (Sigma U) := by
  change (Traces.circle (Sigma.fst : Sigma U → V) univ {root}
    (Fintype.card (Sigma U))).length ≤ _
  simpa only [Finset.card_univ] using
    circle_length_le (Sigma.fst : Sigma U → V) (univ : Finset (Sigma U))
      {root} (Fintype.card (Sigma U))

/-- The edge count of each original record is bounded by the same leg count. -/
theorem program_record_length_le (root : V) (f : Rig.Record U)
    (hf : f ∈ Rig.program U root) :
    f.length ≤ Fintype.card (Sigma U) :=
  circle_record_length_le (Sigma.fst : Sigma U → V)
    (Fintype.card (Sigma U)) univ {root} f hf

end Program

end YM.Integration.FiniteTensorProgramCount
end
