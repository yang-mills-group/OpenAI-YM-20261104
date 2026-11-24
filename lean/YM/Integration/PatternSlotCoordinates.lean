import YM.Integration.PatternTensorRows
import Mathlib.Data.Fintype.EquivFin

/-!
Exact slot coordinates for a fixed original pattern.  The equivalences depend
only on the pattern, and every tensor argument stays at its original Fin slot.
The physical alphabet is Unit.  No sum, norm or price is introduced.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.PatternSlotCoordinates

open Function
open YM.Comparison.RG02
open YM.Integration.PatternTensorRows

abbrev Coupling {n : ℕ} (p : Fin n → Kind) := {k // p k = Kind.coupling}

private lemma kind_select_map {A B : Type} (b : Kind)
    (g : b = .gaussian → A) (c : b = .coupling → A) (p : b = .physical → A)
    (f : A → B) (v : B)
    (hg : ∀ h, f (g h) = v) (hc : ∀ h, f (c h) = v)
    (hp : ∀ h, f (p h) = v) :
    f (match (generalizing := false) h : b with
      | .gaussian => g h
      | .coupling => c h
      | .physical => p h) = v := by
  cases b with
  | gaussian => exact hg rfl
  | coupling => exact hc rfl
  | physical => exact hp rfl

private lemma kind_select_gaussian {A : Type} (b : Kind)
    (g : b = .gaussian → A) (c : b = .coupling → A) (p : b = .physical → A)
    (hb : b = .gaussian) :
    (match (generalizing := false) h : b with
      | .gaussian => g h
      | .coupling => c h
      | .physical => p h) = g hb := by
  cases hb
  rfl

private lemma kind_select_coupling {A : Type} (b : Kind)
    (g : b = .gaussian → A) (c : b = .coupling → A) (p : b = .physical → A)
    (hb : b = .coupling) :
    (match (generalizing := false) h : b with
      | .gaussian => g h
      | .coupling => c h
      | .physical => p h) = c hb := by
  cases hb
  rfl

private lemma kind_select_physical {A : Type} (b : Kind)
    (g : b = .gaussian → A) (c : b = .coupling → A) (p : b = .physical → A)
    (hb : b = .physical) :
    (match (generalizing := false) h : b with
      | .gaussian => g h
      | .coupling => c h
      | .physical => p h) = p hb := by
  cases hb
  rfl

/-- The three original kinds, with their original slot indices. -/
def kindSplit {n : ℕ} (p : Fin n → Kind) :
    Fin n ≃ Coupling p ⊕ (Internal p ⊕ External p) where
  toFun k := match h : p k with
    | .gaussian => Sum.inr (Sum.inl ⟨k, h⟩)
    | .coupling => Sum.inl ⟨k, h⟩
    | .physical => Sum.inr (Sum.inr ⟨k, h⟩)
  invFun := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  left_inv k := by
    exact kind_select_map (A := Coupling p ⊕ (Internal p ⊕ External p)) (p k)
      (fun h => Sum.inr (Sum.inl ⟨k, h⟩))
      (fun h => Sum.inl ⟨k, h⟩)
      (fun h => Sum.inr (Sum.inr ⟨k, h⟩))
      (Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)) k
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  right_inv z := by
    rcases z with u | g | v
    · exact kind_select_coupling (A := Coupling p ⊕ (Internal p ⊕ External p)) (p u.val)
        (fun h => Sum.inr (Sum.inl ⟨u.val, h⟩))
        (fun h => Sum.inl ⟨u.val, h⟩)
        (fun h => Sum.inr (Sum.inr ⟨u.val, h⟩)) u.property
    · exact kind_select_gaussian (A := Coupling p ⊕ (Internal p ⊕ External p)) (p g.val)
        (fun h => Sum.inr (Sum.inl ⟨g.val, h⟩))
        (fun h => Sum.inl ⟨g.val, h⟩)
        (fun h => Sum.inr (Sum.inr ⟨g.val, h⟩)) g.property
    · exact kind_select_physical (A := Coupling p ⊕ (Internal p ⊕ External p)) (p v.val)
        (fun h => Sum.inr (Sum.inl ⟨v.val, h⟩))
        (fun h => Sum.inl ⟨v.val, h⟩)
        (fun h => Sum.inr (Sum.inr ⟨v.val, h⟩)) v.property

/-- A graph-only enumeration of every Gaussian and physical slot. -/
def fieldEquiv {n : ℕ} (p : Fin n → Kind) :
    Fin (Fintype.card (Internal p ⊕ External p)) ≃ Internal p ⊕ External p :=
  (Fintype.equivFin (Internal p ⊕ External p)).symm

/-- Coupling slots followed by the finite field-slot enumeration. -/
def couplingSplit {n : ℕ} (p : Fin n → Kind) :
    Fin n ≃ Coupling p ⊕ Fin (Fintype.card (Internal p ⊕ External p)) :=
  (kindSplit p).trans (Equiv.sumCongr (Equiv.refl _) (fieldEquiv p).symm)

/-- Fixed coupling/Gaussian slots and the physical slots expanded by the
separate multilinear physical-slot theorem. -/
def physicalSplit {n : ℕ} (p : Fin n → Kind) :
    Fin n ≃ (Coupling p ⊕ Internal p) ⊕ External p :=
  (kindSplit p).trans (Equiv.sumAssoc _ _ _).symm

private lemma kind_argument {I C A B E : Type} (b : Kind)
    (c : b = Kind.coupling → C) (g : b = Kind.gaussian → A)
    (p : b = Kind.physical → B) (x : A → I) (f : I → E) (e v : E) :
    Sum.elim f (fun o : Option Unit => o.elim e (fun _ => v))
      (letter (⟨b, match (generalizing := false) h : b with
        | .gaussian => x (g h)
        | .coupling => PUnit.unit
        | .physical => ()⟩ : Σ t, Label I Unit t)) =
    Sum.elim (fun _ : C => e)
      (Sum.elim (fun a : A => f (x a)) (fun _ : B => v))
      (match (generalizing := false) h : b with
        | .gaussian => Sum.inr (Sum.inl (g h))
        | .coupling => Sum.inl (c h)
        | .physical => Sum.inr (Sum.inr (p h))) := by
  cases b <;> rfl

variable {I : Type} [DecidableEq I]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (e : E) (L : (I → ℝ) →ₗ[ℝ] E) (M : (Unit → ℝ) →ₗ[ℝ] E)

/-- Exact original tensor, with each of its three kinds made explicit. -/
theorem tensorValue_kinds {n : ℕ} (p : Fin n → Kind)
    (x : Internal p → I) (T : Tensor.T E ℂ n) :
    PatternTensorRows.tensorValue e L M T ⟨p, (x, fun _ => ())⟩ =
      T (Sum.elim (fun _ : Coupling p => e)
        (Sum.elim (fun g : Internal p => L (Pi.single (x g) 1))
          (fun _ : External p => M (Pi.single () 1))) ∘ kindSplit p) := by
  unfold PatternTensorRows.tensorValue
  apply congrArg (fun v : Fin n → E => T v)
  funext k
  exact kind_argument (p k)
    (fun h => (⟨k, h⟩ : Coupling p))
    (fun h => (⟨k, h⟩ : Internal p))
    (fun h => (⟨k, h⟩ : External p))
    x (fun i => L (Pi.single i 1)) e (M (Pi.single () 1))

/-- The same tensor in coupling-versus-field coordinates.  The finite field
enumeration is independent of all tensor values and coordinate labels. -/
theorem tensorValue_fields {n : ℕ} (p : Fin n → Kind)
    (x : Internal p → I) (T : Tensor.T E ℂ n) :
    PatternTensorRows.tensorValue e L M T ⟨p, (x, fun _ => ())⟩ =
      T (Sum.elim (fun _ : Coupling p => e)
        (fun j => Sum.elim (fun g : Internal p => L (Pi.single (x g) 1))
          (fun _ : External p => M (Pi.single () 1)) (fieldEquiv p j)) ∘
        couplingSplit p) := by
  rw [tensorValue_kinds]
  apply congrArg (fun v : Fin n → E => T v)
  funext k
  cases h : kindSplit p k <;>
    simp [couplingSplit, Equiv.sumCongr, Function.comp_def, h]

/-- Only the physical positions form the second block; all coupling and
Gaussian arguments in the first block are the original fixed arguments. -/
theorem tensorValue_physical {n : ℕ} (p : Fin n → Kind)
    (x : Internal p → I) (T : Tensor.T E ℂ n) :
    PatternTensorRows.tensorValue e L M T ⟨p, (x, fun _ => ())⟩ =
      T (Sum.elim
        (Sum.elim (fun _ : Coupling p => e)
          (fun g : Internal p => L (Pi.single (x g) 1)))
        (fun _ : External p => M (Pi.single () 1)) ∘ physicalSplit p) := by
  rw [tensorValue_kinds]
  apply congrArg (fun v : Fin n → E => T v)
  funext k
  cases h : kindSplit p k with
  | inl c => simp [physicalSplit, Function.comp_def, h]
  | inr f =>
    cases f <;> simp [physicalSplit, Function.comp_def, h]

end YM.Integration.PatternSlotCoordinates
end
