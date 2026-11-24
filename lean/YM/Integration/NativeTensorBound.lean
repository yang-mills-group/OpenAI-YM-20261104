import YM.Integration.AnchoredTensorContractionBound
import YM.Integration.ConnectedTensorGrowth
import YM.Integration.NativeTensorCoordinates

/-!
# The anchored bound for the original connected pairing program

The growth list is chosen from the original ordered diagram before any tensor,
covariance, alphabet, or price is supplied. Every other original edge remains
in the pointwise-cost product. The final program sum retains list multiplicity.
-/

set_option autoImplicit false

noncomputable section

namespace YM.Integration.NativeTensorBound

open YM.Comparison.RG02.Sky
open YM.Integration.AnchoredTensorContraction
open YM.Integration.ConnectedTensorGrowth
open YM.Integration.NativeTensorCoordinates
open scoped BigOperators Classical

variable {V E I : Type} {U : V → Type}

section Graph

variable [Fintype V] [∀ v, Fintype (U v)] [DecidableEq V]
variable [∀ v, DecidableEq (U v)]

/-- This choice depends only on the original graph and its prescribed root. -/
def treeEdges (root : V) (f : Rig.Record U) (hf : f ∈ Rig.program U root) :
    List (Fin f.length) :=
  Classical.choose (program_growth root f hf)

private theorem tree_growth (root : V) (f : Rig.Record U)
    (hf : f ∈ Rig.program U root) :
    Growth (fun j => (f.get j).1.1) (fun j => (f.get j).2.1) root
      (treeEdges root f hf) :=
  (Classical.choose_spec (program_growth root f hf)).1

private theorem tree_cover (root : V) (f : Rig.Record U)
    (hf : f ∈ Rig.program U root) :
    ∀ v, v ∈ root :: (treeEdges root f hf).map (fun j => (f.get j).2.1) :=
  (Classical.choose_spec (program_growth root f hf)).2

def treeCost (root : V) (f : Rig.Record U) (hf : f ∈ Rig.program U root)
    (a : V → ℝ) (b c : Sigma U → Sigma U → ℝ) : ℝ :=
  (∏ v, a v) *
    (∏ j ∈ (treeEdges root f hf).toFinset, b (f.get j).1 (f.get j).2) *
    (∏ j ∈ Finset.univ \ (treeEdges root f hf).toFinset,
      c (f.get j).1 (f.get j).2)

def programCost (root : V) (a : V → ℝ) (b c : Sigma U → Sigma U → ℝ) : ℝ :=
  ∑ k : Fin (Rig.program U root).length,
    treeCost root ((Rig.program U root).get k)
      (List.mem_iff_get.mpr ⟨k, rfl⟩) a b c

end Graph

section NormIdentity

variable [Fintype V] [∀ v, Fintype (U v)] [Fintype E] [Fintype I]

private theorem joint_absolute_eq (π : E → V) (f : Rig.Record U)
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (e0 : E) (i0 : I) :
    jointAbsolute π f A C e0 i0 =
      ∑ z : State π U I, if z (π e0) (.inr ⟨e0, rfl⟩) = i0 then
        (∏ v, ‖A v (z v)‖) *
          (∏ j : Fin f.length, ‖C (f.get j).1 (f.get j).2
            (z (f.get j).1.1 (.inl (f.get j).1.2))
            (z (f.get j).2.1 (.inl (f.get j).2.2))‖)
      else 0 := by
  simp only [jointAbsolute, norm_diagram]

end NormIdentity

section Estimate

variable [Fintype V] [∀ v, Fintype (U v)] [DecidableEq V]
variable [∀ v, DecidableEq (U v)] [Fintype E] [Fintype I]

/-- The native connectedness proof supplies all of the scalar bound's growth
and coverage hypotheses; no stronger graph premise is added. -/
theorem joint_bound (π : E → V) (e0 : E) (i0 : I)
    (f : Rig.Record U) (hf : f ∈ Rig.program U (π e0))
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (b c : Sigma U → Sigma U → ℝ)
    (hA : ∀ v p i, (∑ z : Rig.Pin (U := U) π v → I,
      if z p = i then ‖A v z‖ else 0) ≤ a v)
    (hrow : ∀ j, j ∈ treeEdges (π e0) f hf →
      ∀ i, (∑ i' : I, ‖C (f.get j).1 (f.get j).2 i i'‖) ≤
        b (f.get j).1 (f.get j).2)
    (hpoint : ∀ j, j ∉ treeEdges (π e0) f hf →
      ∀ i i', ‖C (f.get j).1 (f.get j).2 i i'‖ ≤ c (f.get j).1 (f.get j).2) :
    jointAbsolute π f A C e0 i0 ≤ treeCost (π e0) f hf a b c := by
  cases Subsingleton.elim (inferInstance : DecidableEq V)
    (Classical.typeDecidableEq V)
  cases Subsingleton.elim (inferInstance : ∀ v, DecidableEq (U v))
    (fun v => Classical.typeDecidableEq (U v))
  let B : Fin f.length → ℝ := fun j =>
    if j ∈ treeEdges (π e0) f hf then b (f.get j).1 (f.get j).2
    else ∑ i : I, ∑ i' : I, ‖C (f.get j).1 (f.get j).2 i i'‖
  have hB : ∀ j i, (∑ i' : I, ‖C (f.get j).1 (f.get j).2 i i'‖) ≤ B j := by
    intro j i
    by_cases hj : j ∈ treeEdges (π e0) f hf
    · simpa only [B, if_pos hj] using hrow j hj i
    · have hh := Finset.single_le_sum
        (f := fun z : I => ∑ w : I, ‖C (f.get j).1 (f.get j).2 z w‖)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        (Finset.mem_univ i)
      simpa only [B, if_neg hj] using hh
  have hcost : (∏ j ∈ (treeEdges (π e0) f hf).toFinset, B j) =
      ∏ j ∈ (treeEdges (π e0) f hf).toFinset, b (f.get j).1 (f.get j).2 := by
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [B]
    exact if_pos (List.mem_toFinset.mp hj)
  rw [joint_absolute_eq, treeCost, ← hcost]
  exact anchored_tensor_bound (V := V) (J := Fin f.length) (I := I)
    (fun v => Rig.Pin (U := U) π v)
    (fun j : Fin f.length => (f.get j).1.1)
    (fun j : Fin f.length => (f.get j).2.1)
    (fun j => Sum.inl (f.get j).1.2)
    (fun j => Sum.inl (f.get j).2.2)
    A (fun j => C (f.get j).1 (f.get j).2)
    a B
    (fun j => c (f.get j).1 (f.get j).2)
    (π e0) (Sum.inr ⟨e0, rfl⟩) i0
    (tree_growth (π e0) f hf) (tree_cover (π e0) f hf)
    hA hB hpoint

/-- Sum all free external labels of the actual internal contraction while
keeping the prescribed external label fixed. -/
theorem contraction_bound (π : E → V) (e0 : E) (i0 : I)
    (f : Rig.Record U) (hf : f ∈ Rig.program U (π e0))
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (b c : Sigma U → Sigma U → ℝ)
    (hA : ∀ v p i, (∑ z : Rig.Pin (U := U) π v → I,
      if z p = i then ‖A v z‖ else 0) ≤ a v)
    (hrow : ∀ j, j ∈ treeEdges (π e0) f hf →
      ∀ i, (∑ i' : I, ‖C (f.get j).1 (f.get j).2 i i'‖) ≤
        b (f.get j).1 (f.get j).2)
    (hpoint : ∀ j, j ∉ treeEdges (π e0) f hf →
      ∀ i i', ‖C (f.get j).1 (f.get j).2 i i'‖ ≤ c (f.get j).1 (f.get j).2) :
    (∑ x : E → I, if x e0 = i0 then ‖contraction π f A C x‖ else 0) ≤
      treeCost (π e0) f hf a b c :=
  (anchored_le_joint π f A C e0 i0).trans
    (joint_bound π e0 i0 f hf A C a b c hA hrow hpoint)

/-- A row receipt alone also pays every remaining original edge. -/
theorem contraction_row_bound (π : E → V) (e0 : E) (i0 : I)
    (f : Rig.Record U) (hf : f ∈ Rig.program U (π e0))
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (b : Sigma U → Sigma U → ℝ)
    (hA : ∀ v p i, (∑ z : Rig.Pin (U := U) π v → I,
      if z p = i then ‖A v z‖ else 0) ≤ a v)
    (hrow : ∀ p q i, (∑ j : I, ‖C p q i j‖) ≤ b p q) :
    (∑ x : E → I, if x e0 = i0 then ‖contraction π f A C x‖ else 0) ≤
      (∏ v, a v) * (∏ j : Fin f.length, b (f.get j).1 (f.get j).2) := by
  cases Subsingleton.elim (inferInstance : DecidableEq V)
    (Classical.typeDecidableEq V)
  cases Subsingleton.elim (inferInstance : ∀ v, DecidableEq (U v))
    (fun v => Classical.typeDecidableEq (U v))
  apply (anchored_le_joint π f A C e0 i0).trans
  rw [joint_absolute_eq]
  exact anchored_tensor_row_bound (V := V) (J := Fin f.length) (I := I)
    (fun v => Rig.Pin (U := U) π v)
    (fun j : Fin f.length => (f.get j).1.1)
    (fun j : Fin f.length => (f.get j).2.1)
    (fun j => Sum.inl (f.get j).1.2)
    (fun j => Sum.inl (f.get j).2.2)
    A (fun j => C (f.get j).1 (f.get j).2)
    a (fun j => b (f.get j).1 (f.get j).2)
    (π e0) (Sum.inr ⟨e0, rfl⟩) i0
    (tree_growth (π e0) f hf) (tree_cover (π e0) f hf)
    hA (fun j i => hrow (f.get j).1 (f.get j).2 i)

def programContraction (π : E → V) (root : V)
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (x : E → I) : ℂ :=
  ∑ k : Fin (Rig.program U root).length,
    contraction π ((Rig.program U root).get k) A C x

private theorem anchored_sum_bound {J : Type} [Fintype J]
    (F : J → (E → I) → ℂ) (cost : J → ℝ) (e0 : E) (i0 : I)
    (h : ∀ j, (∑ x : E → I, if x e0 = i0 then ‖F j x‖ else 0) ≤ cost j) :
    (∑ x : E → I, if x e0 = i0 then ‖∑ j, F j x‖ else 0) ≤ ∑ j, cost j := by
  calc
    (∑ x : E → I, if x e0 = i0 then ‖∑ j, F j x‖ else 0) ≤
        ∑ x : E → I, ∑ j, if x e0 = i0 then ‖F j x‖ else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x e0 = i0
      · simp only [hx, ite_true]
        exact norm_sum_le _ _
      · simp only [hx, ite_false, Finset.sum_const_zero]
        exact le_rfl
    _ = ∑ j, ∑ x : E → I, if x e0 = i0 then ‖F j x‖ else 0 :=
      Finset.sum_comm
    _ ≤ ∑ j, cost j := Finset.sum_le_sum (fun j _ => h j)

/-- The full finite native program retains every ordered list occurrence.
Each occurrence has its own graph-only growth choice and leftover edges. -/
theorem program_bound (π : E → V) (e0 : E) (i0 : I)
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (b c : Sigma U → Sigma U → ℝ)
    (hA : ∀ v p i, (∑ z : Rig.Pin (U := U) π v → I,
      if z p = i then ‖A v z‖ else 0) ≤ a v)
    (hrow : ∀ k : Fin (Rig.program U (π e0)).length,
      let f := (Rig.program U (π e0)).get k
      ∀ j, j ∈ treeEdges (π e0) f (List.mem_iff_get.mpr ⟨k, rfl⟩) →
        ∀ i, (∑ i' : I, ‖C (f.get j).1 (f.get j).2 i i'‖) ≤
          b (f.get j).1 (f.get j).2)
    (hpoint : ∀ k : Fin (Rig.program U (π e0)).length,
      let f := (Rig.program U (π e0)).get k
      ∀ j, j ∉ treeEdges (π e0) f (List.mem_iff_get.mpr ⟨k, rfl⟩) →
        ∀ i i', ‖C (f.get j).1 (f.get j).2 i i'‖ ≤
          c (f.get j).1 (f.get j).2) :
    (∑ x : E → I,
      if x e0 = i0 then ‖programContraction π (π e0) A C x‖ else 0) ≤
        programCost (π e0) a b c := by
  unfold programContraction programCost
  apply anchored_sum_bound
  intro k
  exact contraction_bound π e0 i0 ((Rig.program U (π e0)).get k)
    (List.mem_iff_get.mpr ⟨k, rfl⟩) A C a b c hA (hrow k) (hpoint k)

/-- With only row costs, the finite pairing contribution is the literal sum
of all original edge-cost products, with no site-alphabet cardinal factor. -/
theorem program_row_bound (π : E → V) (e0 : E) (i0 : I)
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (b : Sigma U → Sigma U → ℝ)
    (hA : ∀ v p i, (∑ z : Rig.Pin (U := U) π v → I,
      if z p = i then ‖A v z‖ else 0) ≤ a v)
    (hrow : ∀ p q i, (∑ j : I, ‖C p q i j‖) ≤ b p q) :
    (∑ x : E → I,
      if x e0 = i0 then ‖programContraction π (π e0) A C x‖ else 0) ≤
        (∏ v, a v) *
          ∑ k : Fin (Rig.program U (π e0)).length,
            ∏ j : Fin ((Rig.program U (π e0)).get k).length,
              b (((Rig.program U (π e0)).get k).get j).1
                (((Rig.program U (π e0)).get k).get j).2 := by
  rw [Finset.mul_sum]
  unfold programContraction
  apply anchored_sum_bound
  intro k
  exact contraction_row_bound π e0 i0 ((Rig.program U (π e0)).get k)
    (List.mem_iff_get.mpr ⟨k, rfl⟩) A C a b hA hrow

end Estimate

end YM.Integration.NativeTensorBound
