import YM.Comparison.RG02.Sky.Rig
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Exact coordinates for an inhomogeneous native diagram

Every internal leg and every external index occurs once in the vertex
configuration. The coordinate equivalence only regroups these indices.
The contraction below retains the full ordered edge list and all tensor
normalizations. Its anchored absolute marginal is bounded by the full
configuration sum using only the finite triangle inequality.
-/

set_option autoImplicit false

noncomputable section

namespace YM.Integration.NativeTensorCoordinates

open YM.Comparison.RG02.Sky
open scoped BigOperators Classical

variable {V E I : Type} {U : V → Type}

abbrev State (π : E → V) (P : V → Type) (X : Type) :=
  ∀ v, Rig.Pin (U := P) π v → X

def coordinates (π : E → V) :
    State π U I ≃ ((Sigma U → I) × (E → I)) where
  toFun z :=
    (fun p => z p.1 (.inl p.2),
     fun e => z (π e) (.inr ⟨e, rfl⟩))
  invFun y v := Sum.elim (fun p => y.1 ⟨v, p⟩) (fun e => y.2 e.val)
  left_inv z := by
    funext v p
    cases p with
    | inl p => rfl
    | inr e =>
      rcases e with ⟨e, he⟩
      cases he
      rfl
  right_inv y := by
    rcases y with ⟨u, x⟩
    apply Prod.ext
    · funext p
      cases p
      rfl
    · rfl

variable (π : E → V)

theorem coordinates_external (z : State π U I) (e : E) :
    (coordinates π z).2 e = z (π e) (.inr ⟨e, rfl⟩) := rfl

def diagram [Fintype V] (f : Rig.Record U)
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (z : State π U I) : ℂ :=
  (∏ v, A v (z v)) *
    ∏ j : Fin f.length,
      C (f.get j).1 (f.get j).2
        (z (f.get j).1.1 (.inl (f.get j).1.2))
        (z (f.get j).2.1 (.inl (f.get j).2.2))

theorem norm_diagram [Fintype V] (f : Rig.Record U)
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (z : State π U I) :
    ‖diagram π f A C z‖ =
      (∏ v, ‖A v (z v)‖) *
        ∏ j : Fin f.length,
          ‖C (f.get j).1 (f.get j).2
            (z (f.get j).1.1 (.inl (f.get j).1.2))
            (z (f.get j).2.1 (.inl (f.get j).2.2))‖ := by
  simp only [diagram, norm_mul, norm_prod]

def contraction [Fintype V] [∀ v, Fintype (U v)] [Fintype I]
    (f : Rig.Record U) (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (x : E → I) : ℂ :=
  ∑ u : Sigma U → I, diagram π f A C ((coordinates π).symm (u, x))

def jointAbsolute [Fintype V] [∀ v, Fintype (U v)]
    [Fintype E] [Fintype I] (f : Rig.Record U)
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (e0 : E) (i0 : I) : ℝ :=
  ∑ z : State π U I,
    if z (π e0) (.inr ⟨e0, rfl⟩) = i0 then ‖diagram π f A C z‖ else 0

theorem anchored_le_joint [Fintype V] [∀ v, Fintype (U v)]
    [Fintype E] [Fintype I] (f : Rig.Record U)
    (A : ∀ v, (Rig.Pin (U := U) π v → I) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (e0 : E) (i0 : I) :
    (∑ x : E → I,
      if x e0 = i0 then ‖contraction π f A C x‖ else 0) ≤
        jointAbsolute π f A C e0 i0 := by
  let F : ((Sigma U → I) × (E → I)) → ℝ :=
    fun p => if p.2 e0 = i0 then
      ‖diagram π f A C ((coordinates π).symm p)‖ else 0
  calc
    (∑ x : E → I,
      if x e0 = i0 then ‖contraction π f A C x‖ else 0) ≤
        ∑ x : E → I, ∑ u : Sigma U → I, F (u, x) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x e0 = i0
      · simp only [F, hx, ite_true, contraction]
        exact norm_sum_le _ _
      · simp only [F, hx, ite_false, Finset.sum_const_zero]
        exact le_rfl
    _ = ∑ p, F p := (Fintype.sum_prod_type_right F).symm
    _ = ∑ z : State π U I, F (coordinates π z) :=
      (Equiv.sum_comp (coordinates π) F).symm
    _ = jointAbsolute π f A C e0 i0 := by
      unfold jointAbsolute
      apply Finset.sum_congr rfl
      intro z _
      dsimp only [F]
      rw [Equiv.symm_apply_apply, coordinates_external]

end YM.Integration.NativeTensorCoordinates
