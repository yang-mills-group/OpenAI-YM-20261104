import YM.Comparison.RG02.Sky.Rig
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Separate Gaussian and physical coordinates in a finite diagram

Every vertex keeps its internal Gaussian ports and its physical external
ports in distinct finite alphabets. Fixed coupling slots are already part
of the vertex tensor and add no summation coordinate here.
-/

set_option autoImplicit false

noncomputable section

namespace YM.Integration.HeterogeneousTensorCoordinates

open YM.Comparison.RG02.Sky
open scoped BigOperators Classical

variable {V I J : Type} {U E : V → Type}

abbrev State (U E : V → Type) (I J : Type) :=
  ∀ v, (U v → I) × (E v → J)

def coordinates : State U E I J ≃ ((Sigma U → I) × (Sigma E → J)) where
  toFun z :=
    (fun p => (z p.1).1 p.2, fun e => (z e.1).2 e.2)
  invFun y v := (fun p => y.1 ⟨v, p⟩, fun e => y.2 ⟨v, e⟩)
  left_inv z := by
    funext v
    exact Prod.ext rfl rfl
  right_inv y := by
    rcases y with ⟨u, x⟩
    apply Prod.ext
    · funext p
      cases p
      rfl
    · funext e
      cases e
      rfl

theorem coordinates_external (z : State U E I J) (e : Sigma E) :
    (coordinates z).2 e = (z e.1).2 e.2 := rfl

def diagram [Fintype V] (f : Rig.Record U)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (z : State U E I J) : ℂ :=
  (∏ v, A v (z v)) *
    ∏ k : Fin f.length,
      C (f.get k).1 (f.get k).2
        ((z (f.get k).1.1).1 (f.get k).1.2)
        ((z (f.get k).2.1).1 (f.get k).2.2)

theorem norm_diagram [Fintype V] (f : Rig.Record U)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (z : State U E I J) :
    ‖diagram f A C z‖ =
      (∏ v, ‖A v (z v)‖) *
        ∏ k : Fin f.length,
          ‖C (f.get k).1 (f.get k).2
            ((z (f.get k).1.1).1 (f.get k).1.2)
            ((z (f.get k).2.1).1 (f.get k).2.2)‖ := by
  simp only [diagram, norm_mul, norm_prod]

def contraction [Fintype V] [∀ v, Fintype (U v)] [Fintype I]
    (f : Rig.Record U) (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (x : Sigma E → J) : ℂ :=
  ∑ u : Sigma U → I, diagram f A C (coordinates.symm (u, x))

def jointAbsolute [Fintype V] [∀ v, Fintype (U v)]
    [∀ v, Fintype (E v)] [Fintype I] [Fintype J] (f : Rig.Record U)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (e0 : Sigma E) (j0 : J) : ℝ :=
  ∑ z : State U E I J,
    if (z e0.1).2 e0.2 = j0 then ‖diagram f A C z‖ else 0

theorem anchored_le_joint [Fintype V] [∀ v, Fintype (U v)]
    [∀ v, Fintype (E v)] [Fintype I] [Fintype J] (f : Rig.Record U)
    (A : ∀ v, ((U v → I) × (E v → J)) → ℂ)
    (C : Sigma U → Sigma U → I → I → ℂ) (e0 : Sigma E) (j0 : J) :
    (∑ x : Sigma E → J,
      if x e0 = j0 then ‖contraction f A C x‖ else 0) ≤
        jointAbsolute f A C e0 j0 := by
  let F : ((Sigma U → I) × (Sigma E → J)) → ℝ :=
    fun p => if p.2 e0 = j0 then
      ‖diagram f A C (coordinates.symm p)‖ else 0
  calc
    (∑ x : Sigma E → J,
      if x e0 = j0 then ‖contraction f A C x‖ else 0) ≤
        ∑ x : Sigma E → J, ∑ u : Sigma U → I, F (u, x) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x e0 = j0
      · simp only [F, hx, ite_true, contraction]
        exact norm_sum_le _ _
      · simp only [F, hx, ite_false, Finset.sum_const_zero]
        exact le_rfl
    _ = ∑ p, F p := (Fintype.sum_prod_type_right F).symm
    _ = ∑ z : State U E I J, F (coordinates z) :=
      (Equiv.sum_comp coordinates F).symm
    _ = jointAbsolute f A C e0 j0 := by
      unfold jointAbsolute
      apply Finset.sum_congr rfl
      intro z _
      dsimp only [F]
      rw [Equiv.symm_apply_apply, coordinates_external]

end YM.Integration.HeterogeneousTensorCoordinates

end
