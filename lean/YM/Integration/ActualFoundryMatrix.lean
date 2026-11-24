import YM.Integration.NativeSignedBranches

/-!
Literal mixed-degree physical columns and their unit padding, independent
of the heavier Foundry trajectory producer. Every entry stays in the same
Family, with its original origin and Motion. A padding entry is the actual
calibrated observable refUnit, whose value is proved to be one.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualFoundryInitialization
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent Extra.Histories
open scoped Classical BigOperators

variable {G : Gauge}

/-- A padding unit is an actual calibrated observable in the same family.
Its motion and declared origin stay in the original source table. -/
theorem item_refUnit (C : Family G) (hC : C.Makes) (N p d : ℕ)
    (hd : C.ref d ≤ N) (o : ∀ m, Site (C.side m p)) (z : Motion) :
    item C d N p (C.refUnit d) o z = 1 := by
  unfold item
  rw [C.constant hC d hd]
  funext U
  simp [stepUp, Motion.scalar]

variable {I : Type} [Fintype I] [DecidableEq I] {arity : ℕ}

/-- Product factors and the compensating column keep their original
labels. Only the explicitly padded positions use this family's unit. -/
def matrixToken (C : Family G)
    (v : I → Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : I → (d : ℕ) × C.label d) (unitDegree : ℕ)
    (a : Replicum.Name arity (NativeSignedBranches.Branch I)) :
    (d : ℕ) × C.label d :=
  if a.1.2 then v a.1.1 a.2
  else if a.2 = 0 then z a.1.1 else ⟨unitDegree, C.refUnit unitDegree⟩

/-- The complete native marked source is exactly the physical matrix of
product factors, one counterterm per branch, and literal unit padding. -/
theorem matrix_topJoint (C : Family G) (hC : C.Makes) (N p : ℕ)
    (v : I → Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : I → (d : ℕ) × C.label d) (unitDegree : ℕ)
    (hUnit : C.ref unitDegree ≤ N)
    (o : ∀ m, Replicum.Name arity (NativeSignedBranches.Branch I) →
      Site (C.side m p))
    (motion : Replicum.Name arity (NativeSignedBranches.Branch I) → Motion) :
    let t := matrixToken C v z unitDegree
    let F := fun i j => item C (v i j).1 N p (v i j).2
      (fun m => o m ((i, true), j)) (motion ((i, true), j))
    let K := fun i => item C (z i).1 N p (z i).2
      (fun m => o m ((i, false), 0)) (motion ((i, false), 0))
    PhysicalJoin.Marked.topJoint (fun a => (t a).1) (fun a => (t a).2)
      o motion (Replicum.Aged arity (NativeSignedBranches.Branch I)) N =
      birth (Replicum.Aged arity (NativeSignedBranches.Branch I))
        (C.path.rep N p N) (NativeSignedBranches.matrix F K) := by
  intro t F K
  unfold PhysicalJoin.Marked.topJoint
  congr 1
  funext a U
  rcases a with ⟨⟨i, b⟩, j⟩
  cases b
  · by_cases hj : j = 0
    · subst j
      rfl
    · have ht : t ((i, false), j) = ⟨unitDegree, C.refUnit unitDegree⟩ := by
        simp [t, matrixToken, hj]
      change item C (t ((i, false), j)).1 N p (t ((i, false), j)).2
        (fun m => o m ((i, false), j)) (motion ((i, false), j)) U =
          if j = 0 then K i U else 1
      rw [if_neg hj, ht]
      exact congr_fun (item_refUnit C hC N p unitDegree hUnit
        (fun m => o m ((i, false), j)) (motion ((i, false), j))) U
  · rfl

end YM.Integration.ActualFoundryInitialization
