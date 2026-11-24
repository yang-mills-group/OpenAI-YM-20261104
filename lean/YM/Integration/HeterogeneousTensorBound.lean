import YM.Integration.NativeTensorBound
import YM.Integration.HeterogeneousTensorCoordinates
import YM.Integration.AnchoredTensorObservation

/-!
# Native connected diagrams with separate Gaussian and physical alphabets

The graph-only growth choice is unchanged. Selected edges use their incoming
Gaussian fiber and row bounds; all other original edges use pointwise costs.
An actual internal assignment supplies the observation theorem's baseline.
The final contraction and program bounds also cover empty assignment types,
using only the stated nonnegative prices in that zero-sum branch.
-/

set_option autoImplicit false

noncomputable section

namespace YM.Integration.HeterogeneousTensorBound

open YM.Comparison.RG02.Sky
open YM.Integration.AnchoredTensorContraction
open YM.Integration.ConnectedTensorGrowth
open YM.Integration.HeterogeneousTensorCoordinates
open YM.Integration.NativeTensorBound (treeEdges treeCost programCost)
open scoped BigOperators Classical

variable {V I J : Type} {U E : V → Type}

section NormIdentity

variable [Fintype V] [∀ v, Fintype (U v)] [∀ v, Fintype (E v)]
variable [Fintype I] [Fintype J]

private theorem joint_absolute_eq (f : Rig.Record U)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (e0 : Sigma E) (j0 : J) :
    jointAbsolute f A C e0 j0 =
      ∑ z : State U E I J, if (z e0.1).2 e0.2 = j0 then
        (∏ v, ‖A v (z v)‖) *
          (∏ k : Fin f.length, ‖C (f.get k).1 (f.get k).2
            ((z (f.get k).1.1).1 (f.get k).1.2)
            ((z (f.get k).2.1).1 (f.get k).2.2)‖)
      else 0 := by
  simp only [jointAbsolute, norm_diagram]

end NormIdentity

variable [Fintype V] [∀ v, Fintype (U v)] [DecidableEq V]
variable [∀ v, DecidableEq (U v)]

private theorem tree_growth (root : V) (f : Rig.Record U)
    (hf : f ∈ Rig.program U root) :
    Growth (fun k => (f.get k).1.1) (fun k => (f.get k).2.1) root
      (treeEdges root f hf) :=
  (Classical.choose_spec (program_growth root f hf)).1

private theorem tree_cover (root : V) (f : Rig.Record U)
    (hf : f ∈ Rig.program U root) :
    ∀ v, v ∈ root :: (treeEdges root f hf).map (fun k => (f.get k).2.1) :=
  (Classical.choose_spec (program_growth root f hf)).2

private theorem cost_nonneg (root : V) (f : Rig.Record U)
    (hf : f ∈ Rig.program U root) (a : V → ℝ)
    (b c : Sigma U → Sigma U → ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ p q, 0 ≤ b p q)
    (hc : ∀ p q, 0 ≤ c p q) :
    0 ≤ treeCost root f hf a b c := by
  unfold treeCost
  exact mul_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun v _ => ha v))
      (Finset.prod_nonneg (fun k _ => hb (f.get k).1 (f.get k).2)))
    (Finset.prod_nonneg (fun k _ => hc (f.get k).1 (f.get k).2))

section Estimate

variable [∀ v, Fintype (E v)] [Fintype I] [Fintype J]

/-- Any original internal assignment gives a baseline without identifying
the Gaussian alphabet with the physical one. -/
theorem joint_bound (e0 : Sigma E) (j0 : J) (u0 : Sigma U → I)
    (f : Rig.Record U) (hf : f ∈ Rig.program U e0.1)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (b c : Sigma U → Sigma U → ℝ)
    (hroot : (∑ z : (U e0.1 → I) × (E e0.1 → J),
      if z.2 e0.2 = j0 then ‖A e0.1 z‖ else 0) ≤ a e0.1)
    (hA : ∀ k, k ∈ treeEdges e0.1 f hf → ∀ i,
      (∑ z : (U (f.get k).2.1 → I) × (E (f.get k).2.1 → J),
        if z.1 (f.get k).2.2 = i then ‖A (f.get k).2.1 z‖ else 0) ≤
          a (f.get k).2.1)
    (hrow : ∀ k, k ∈ treeEdges e0.1 f hf → ∀ i,
      (∑ i' : I, ‖C (f.get k).1 (f.get k).2 i i'‖) ≤
        b (f.get k).1 (f.get k).2)
    (hpoint : ∀ k, k ∉ treeEdges e0.1 f hf → ∀ i i',
      ‖C (f.get k).1 (f.get k).2 i i'‖ ≤ c (f.get k).1 (f.get k).2) :
    jointAbsolute f A C e0 j0 ≤ treeCost e0.1 f hf a b c := by
  cases Subsingleton.elim (inferInstance : DecidableEq V)
    (Classical.typeDecidableEq V)
  cases Subsingleton.elim (inferInstance : ∀ v, DecidableEq (U v))
    (fun v => Classical.typeDecidableEq (U v))
  rw [joint_absolute_eq, treeCost]
  let X : V → Type := fun v => (U v → I) × (E v → J)
  let base : ∀ v, X v := fun v => (fun p => u0 ⟨v, p⟩, fun _ => j0)
  exact AnchoredTensorObservation.anchored_observation_bound
    (V := V) (E := Fin f.length) (I := I)
    X (fun k : Fin f.length => (f.get k).1.1)
    (fun k : Fin f.length => (f.get k).2.1)
    (fun k z => z.1 (f.get k).1.2)
    (fun k z => z.1 (f.get k).2.2)
    A (fun k => C (f.get k).1 (f.get k).2)
    a (fun k => b (f.get k).1 (f.get k).2)
    (fun k => c (f.get k).1 (f.get k).2)
    e0.1 (fun z => z.2 e0.2 = j0) base
    (tree_growth e0.1 f hf) (tree_cover e0.1 f hf)
    hroot hA hrow hpoint

/-- The actual anchored contraction bound includes empty internal assignment
types. Nonnegative prices suffice in that branch, where every internal sum is zero. -/
theorem contraction_bound (e0 : Sigma E) (j0 : J)
    (f : Rig.Record U) (hf : f ∈ Rig.program U e0.1)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (b c : Sigma U → Sigma U → ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ p q, 0 ≤ b p q)
    (hc : ∀ p q, 0 ≤ c p q)
    (hroot : (∑ z : (U e0.1 → I) × (E e0.1 → J),
      if z.2 e0.2 = j0 then ‖A e0.1 z‖ else 0) ≤ a e0.1)
    (hA : ∀ k, k ∈ treeEdges e0.1 f hf → ∀ i,
      (∑ z : (U (f.get k).2.1 → I) × (E (f.get k).2.1 → J),
        if z.1 (f.get k).2.2 = i then ‖A (f.get k).2.1 z‖ else 0) ≤
          a (f.get k).2.1)
    (hrow : ∀ k, k ∈ treeEdges e0.1 f hf → ∀ i,
      (∑ i' : I, ‖C (f.get k).1 (f.get k).2 i i'‖) ≤
        b (f.get k).1 (f.get k).2)
    (hpoint : ∀ k, k ∉ treeEdges e0.1 f hf → ∀ i i',
      ‖C (f.get k).1 (f.get k).2 i i'‖ ≤ c (f.get k).1 (f.get k).2) :
    (∑ x : Sigma E → J, if x e0 = j0 then ‖contraction f A C x‖ else 0) ≤
      treeCost e0.1 f hf a b c := by
  cases Subsingleton.elim (inferInstance : DecidableEq V)
    (Classical.typeDecidableEq V)
  cases Subsingleton.elim (inferInstance : ∀ v, DecidableEq (U v))
    (fun v => Classical.typeDecidableEq (U v))
  by_cases hU : Nonempty (Sigma U → I)
  · obtain ⟨u0⟩ := hU
    exact (anchored_le_joint f A C e0 j0).trans
      (joint_bound e0 j0 u0 f hf A C a b c hroot hA hrow hpoint)
  · letI : IsEmpty (Sigma U → I) := ⟨fun u => hU ⟨u⟩⟩
    simpa [contraction] using cost_nonneg e0.1 f hf a b c ha hb hc

def programContraction (root : V)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (x : Sigma E → J) : ℂ :=
  ∑ k : Fin (Rig.program U root).length,
    contraction ((Rig.program U root).get k) A C x

private theorem anchored_sum_bound {K : Type} [Fintype K]
    (F : K → (Sigma E → J) → ℂ) (cost : K → ℝ) (e0 : Sigma E) (j0 : J)
    (h : ∀ k, (∑ x : Sigma E → J, if x e0 = j0 then ‖F k x‖ else 0) ≤ cost k) :
    (∑ x : Sigma E → J, if x e0 = j0 then ‖∑ k, F k x‖ else 0) ≤ ∑ k, cost k := by
  calc
    (∑ x : Sigma E → J, if x e0 = j0 then ‖∑ k, F k x‖ else 0) ≤
        ∑ x : Sigma E → J, ∑ k, if x e0 = j0 then ‖F k x‖ else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x e0 = j0
      · simp only [hx, ite_true]
        exact norm_sum_le _ _
      · simp only [hx, ite_false, Finset.sum_const_zero]
        exact le_rfl
    _ = ∑ k, ∑ x : Sigma E → J, if x e0 = j0 then ‖F k x‖ else 0 :=
      Finset.sum_comm
    _ ≤ ∑ k, cost k := Finset.sum_le_sum (fun k _ => h k)

/-- Every original ordered program entry remains in the sum. Gaussian and
physical labels remain separate, including the empty Gaussian-index case. -/
theorem program_bound (e0 : Sigma E) (j0 : J)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ)
    (a : V → ℝ) (b c : Sigma U → Sigma U → ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ p q, 0 ≤ b p q)
    (hc : ∀ p q, 0 ≤ c p q)
    (hroot : (∑ z : (U e0.1 → I) × (E e0.1 → J),
      if z.2 e0.2 = j0 then ‖A e0.1 z‖ else 0) ≤ a e0.1)
    (hA : ∀ k : Fin (Rig.program U e0.1).length,
      let f := (Rig.program U e0.1).get k
      ∀ l, l ∈ treeEdges e0.1 f (List.mem_iff_get.mpr ⟨k, rfl⟩) → ∀ i,
        (∑ z : (U (f.get l).2.1 → I) × (E (f.get l).2.1 → J),
          if z.1 (f.get l).2.2 = i then ‖A (f.get l).2.1 z‖ else 0) ≤
            a (f.get l).2.1)
    (hrow : ∀ k : Fin (Rig.program U e0.1).length,
      let f := (Rig.program U e0.1).get k
      ∀ l, l ∈ treeEdges e0.1 f (List.mem_iff_get.mpr ⟨k, rfl⟩) → ∀ i,
        (∑ i' : I, ‖C (f.get l).1 (f.get l).2 i i'‖) ≤
          b (f.get l).1 (f.get l).2)
    (hpoint : ∀ k : Fin (Rig.program U e0.1).length,
      let f := (Rig.program U e0.1).get k
      ∀ l, l ∉ treeEdges e0.1 f (List.mem_iff_get.mpr ⟨k, rfl⟩) → ∀ i i',
        ‖C (f.get l).1 (f.get l).2 i i'‖ ≤ c (f.get l).1 (f.get l).2) :
    (∑ x : Sigma E → J,
      if x e0 = j0 then ‖programContraction e0.1 A C x‖ else 0) ≤
        programCost e0.1 a b c := by
  unfold programContraction programCost
  apply anchored_sum_bound
  intro k
  exact contraction_bound e0 j0 ((Rig.program U e0.1).get k)
    (List.mem_iff_get.mpr ⟨k, rfl⟩) A C a b c ha hb hc hroot
    (hA k) (hrow k) (hpoint k)

end Estimate

end YM.Integration.HeterogeneousTensorBound

end
