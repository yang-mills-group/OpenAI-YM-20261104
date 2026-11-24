import YM.Integration.HeterogeneousTensorBound
import YM.Integration.FiniteTensorProgramCount

/-!
# Uniform costs for the complete native anchored program

Every original program-list occurrence remains. The same price B is used
for selected row costs and the remaining pointwise costs; their products
recombine without division, so no edge or loop is deleted.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FiniteTensorProgramCost

open Finset
open YM.Comparison.RG02.Sky
open YM.Integration.NativeTensorBound (treeEdges treeCost programCost)
open YM.Integration.HeterogeneousTensorCoordinates
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V]
variable {U : V → Type} [∀ v, Fintype (U v)] [∀ v, DecidableEq (U v)]

/-- The selected and remaining products contain every original edge once. -/
theorem tree_cost_uniform (root : V) (f : Rig.Record U)
    (hf : f ∈ Rig.program U root) (a : V → ℝ) (B : ℝ) :
    treeCost root f hf a (fun _ _ => B) (fun _ _ => B) =
      (∏ v, a v) * B ^ f.length := by
  have hp :
      (∏ j ∈ (treeEdges root f hf).toFinset, B) *
        (∏ j ∈ univ \ (treeEdges root f hf).toFinset, B) =
      B ^ f.length := by
    calc
      _ = ∏ _j : Fin f.length, B :=
        Finset.prod_mul_prod_compl (treeEdges root f hf).toFinset (fun _ => B)
      _ = _ := by simp
  simpa only [treeCost, mul_assoc] using congrArg ((∏ v, a v) * ·) hp

/-- A leg-count bound gives an alphabet-independent bound on the full program. -/
theorem program_cost_uniform (root : V) (a : V → ℝ) (B : ℝ) (N : ℕ)
    (ha : ∀ v, 0 ≤ a v) (hB : 1 ≤ B) (hN : Fintype.card (Sigma U) ≤ N) :
    programCost (U := U) root a (fun _ _ => B) (fun _ _ => B) ≤
      (((N + 1) ^ N : ℕ) : ℝ) * (∏ v, a v) * B ^ N := by
  have hP : 0 ≤ ∏ v, a v := Finset.prod_nonneg (fun v _ => ha v)
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hlen : (Rig.program U root).length ≤ (N + 1) ^ N := by
    calc
      _ ≤ (Fintype.card (Sigma U) + 1) ^ Fintype.card (Sigma U) :=
        FiniteTensorProgramCount.program_length_le U root
      _ ≤ (N + 1) ^ Fintype.card (Sigma U) :=
        Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) _
      _ ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) hN
  unfold programCost
  calc
    _ ≤ ∑ _k : Fin (Rig.program U root).length, (∏ v, a v) * B ^ N := by
      apply Finset.sum_le_sum
      intro k _
      rw [tree_cost_uniform]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hB
          ((FiniteTensorProgramCount.program_record_length_le U root _
            (List.mem_iff_get.mpr ⟨k, rfl⟩)).trans hN)) hP
    _ = ((Rig.program U root).length : ℝ) * ((∏ v, a v) * B ^ N) := by
      simp
    _ ≤ (((N + 1) ^ N : ℕ) : ℝ) * ((∏ v, a v) * B ^ N) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlen)
        (mul_nonneg hP (pow_nonneg hB0 N))
    _ = _ := (mul_assoc _ _ _).symm

section UnitExternal

variable {I : Type} [Fintype I]
variable {E : V → Type} [∀ v, Fintype (E v)]

/-- The one-direction external alphabet retains the real physical anchor.
The Gaussian alphabet remains arbitrary, including the empty case. -/
theorem unit_program_bound (e0 : Sigma E)
    (A : ∀ v, ((U v → I) × (E v → Unit)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (B : ℝ) (N : ℕ)
    (ha : ∀ v, 0 ≤ a v) (hB : 1 ≤ B) (hN : Fintype.card (Sigma U) ≤ N)
    (hroot : (∑ z : (U e0.1 → I) × (E e0.1 → Unit), ‖A e0.1 z‖) ≤ a e0.1)
    (hA : ∀ k : Fin (Rig.program U e0.1).length,
      let f := (Rig.program U e0.1).get k
      ∀ l, l ∈ treeEdges e0.1 f (List.mem_iff_get.mpr ⟨k, rfl⟩) → ∀ i,
        (∑ z : (U (f.get l).2.1 → I) × (E (f.get l).2.1 → Unit),
          if z.1 (f.get l).2.2 = i then ‖A (f.get l).2.1 z‖ else 0) ≤
            a (f.get l).2.1)
    (hrow : ∀ k : Fin (Rig.program U e0.1).length,
      let f := (Rig.program U e0.1).get k
      ∀ l, l ∈ treeEdges e0.1 f (List.mem_iff_get.mpr ⟨k, rfl⟩) → ∀ i,
        (∑ i' : I, ‖C (f.get l).1 (f.get l).2 i i'‖) ≤ B)
    (hpoint : ∀ k : Fin (Rig.program U e0.1).length,
      let f := (Rig.program U e0.1).get k
      ∀ l, l ∉ treeEdges e0.1 f (List.mem_iff_get.mpr ⟨k, rfl⟩) → ∀ i i',
        ‖C (f.get l).1 (f.get l).2 i i'‖ ≤ B) :
    ‖HeterogeneousTensorBound.programContraction e0.1 A C (fun _ => ())‖ ≤
      (((N + 1) ^ N : ℕ) : ℝ) * (∏ v, a v) * B ^ N := by
  have h := HeterogeneousTensorBound.program_bound e0 () A C a
    (fun _ _ => B) (fun _ _ => B) ha
    (fun _ _ => le_trans zero_le_one hB) (fun _ _ => le_trans zero_le_one hB)
    (by
      simpa only [show ∀ z : (U e0.1 → I) × (E e0.1 → Unit),
        z.2 e0.2 = () from fun _ => Subsingleton.elim _ _, ite_true] using hroot)
    hA hrow hpoint
  have he (x : Sigma E → Unit) : x e0 = () := Subsingleton.elim _ _
  have hh : ‖HeterogeneousTensorBound.programContraction e0.1 A C (fun _ => ())‖ ≤
      programCost (U := U) e0.1 a (fun _ _ => B) (fun _ _ => B) := by
    simpa only [he, ite_true, Fintype.sum_unique] using h
  exact hh.trans (program_cost_uniform (U := U) e0.1 a B N ha hB hN)

end UnitExternal

end YM.Integration.FiniteTensorProgramCost
end
