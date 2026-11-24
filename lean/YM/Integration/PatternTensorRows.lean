import YM.Integration.NativeTensorRows

/-!
# Fixed slot patterns and separate Gaussian and physical configurations

The three slot kinds retain their original ordered positions. A coupling
slot has exactly one label; it contributes the fixed coupling direction.
Gaussian and physical slots have independent index types. The finite
equivalences below only regroup the complete wordL sum.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.PatternTensorRows

open Finset Function
open YM.Next.Rank YM.Comparison.RG02
open YM.Integration.FiniteConnectedProgram
open YM.Integration.NativeTensorRows (Alphabet)
open scoped BigOperators

inductive Kind
  | gaussian
  | coupling
  | physical
  deriving DecidableEq, Fintype

def Label (I J : Type) : Kind → Type
  | .gaussian => I
  | .coupling => PUnit
  | .physical => J

instance {I J : Type} [Fintype I] [Fintype J] (k : Kind) :
    Fintype (Label I J k) := by
  cases k <;> dsimp only [Label] <;> infer_instance

def letter {I J : Type} : (Σ k, Label I J k) ≃ Alphabet I J where
  toFun
    | ⟨.gaussian, i⟩ => Sum.inl i
    | ⟨.coupling, _⟩ => Sum.inr none
    | ⟨.physical, j⟩ => Sum.inr (some j)
  invFun
    | Sum.inl i => ⟨.gaussian, i⟩
    | Sum.inr none => ⟨.coupling, PUnit.unit⟩
    | Sum.inr (some j) => ⟨.physical, j⟩
  left_inv z := by
    rcases z with ⟨k, x⟩
    cases k with
    | gaussian => rfl
    | coupling => cases x; rfl
    | physical => rfl
  right_inv z := by
    rcases z with i | (_ | j) <;> rfl

def piSigma {A : Type} {B : A → Type} {C : ∀ a, B a → Type} :
    (∀ a, Σ b, C a b) ≃ (Σ b : ∀ a, B a, ∀ a, C a (b a)) where
  toFun z := ⟨fun a => (z a).1, fun a => (z a).2⟩
  invFun z a := ⟨z.1 a, z.2 a⟩
  left_inv z := by
    funext a
    exact Sigma.eta (z a)
  right_inv z := by
    rcases z with ⟨b, c⟩
    rfl

abbrev Internal {n : ℕ} (s : Fin n → Kind) := {k // s k = Kind.gaussian}
abbrev External {n : ℕ} (s : Fin n → Kind) := {k // s k = Kind.physical}
abbrev State {n : ℕ} (s : Fin n → Kind) (I J : Type) :=
  (Internal s → I) × (External s → J)

def stateOf {I J : Type} {n : ℕ} (s : Fin n → Kind)
    (a : ∀ k, Label I J (s k)) : State s I J :=
  (fun u => cast (congrArg (Label I J) u.property) (a u.val),
    fun u => cast (congrArg (Label I J) u.property) (a u.val))

def labelsOf {I J : Type} {n : ℕ} (s : Fin n → Kind)
    (z : State s I J) : ∀ k, Label I J (s k) :=
  fun k => match h : s k with
  | .gaussian => z.1 ⟨k, h⟩
  | .coupling => PUnit.unit
  | .physical => z.2 ⟨k, h⟩

private lemma kind_eta {I J : Type} (b : Kind) (a : Label I J b) :
    (show Label I J b from match (generalizing := false) h : b with
    | .gaussian => cast (congrArg (Label I J) h) a
    | .coupling => PUnit.unit
    | .physical => cast (congrArg (Label I J) h) a) = a := by
  cases b with
  | gaussian => rfl
  | coupling => cases a; rfl
  | physical => rfl

private lemma kind_gaussian {I J : Type} (b : Kind)
    (g : b = .gaussian → I) (p : b = .physical → J) (hb : b = .gaussian) :
    cast (congrArg (Label I J) hb)
      (show Label I J b from match (generalizing := false) h : b with
      | .gaussian => g h
      | .coupling => PUnit.unit
      | .physical => p h) = g hb := by
  cases hb
  rfl

private lemma kind_physical {I J : Type} (b : Kind)
    (g : b = .gaussian → I) (p : b = .physical → J) (hb : b = .physical) :
    cast (congrArg (Label I J) hb)
      (show Label I J b from match (generalizing := false) h : b with
      | .gaussian => g h
      | .coupling => PUnit.unit
      | .physical => p h) = p hb := by
  cases hb
  rfl

def localCoordinates {I J : Type} {n : ℕ} (s : Fin n → Kind) :
    (∀ k, Label I J (s k)) ≃ State s I J where
  toFun := stateOf s
  invFun := labelsOf s
  left_inv a := by
    funext k
    exact kind_eta (s k) (a k)
  right_inv z := by
    apply Prod.ext
    · funext u
      exact kind_gaussian (s u.val)
        (fun h => z.1 ⟨u.val, h⟩) (fun h => z.2 ⟨u.val, h⟩) u.property
    · funext u
      exact kind_physical (s u.val)
        (fun h => z.1 ⟨u.val, h⟩) (fun h => z.2 ⟨u.val, h⟩) u.property

abbrev Choice (I J : Type) (n : ℕ) := Σ s : Fin n → Kind, State s I J

def choiceEquiv {I J : Type} (n : ℕ) :
    (Fin n → Alphabet I J) ≃ Choice I J n :=
  (Equiv.piCongrRight (fun _ => letter.symm)).trans
    (piSigma.trans (Equiv.sigmaCongrRight (fun s => localCoordinates s)))

def decode {I J : Type} {n : ℕ} (c : Choice I J n) : Fin n → Alphabet I J :=
  fun k => letter ⟨c.1 k, labelsOf c.1 c.2 k⟩

private lemma choice_decode {I J : Type} {n : ℕ} (c : Choice I J n) :
    (choiceEquiv n).symm c = decode c := rfl

private lemma letter_gaussian {I J : Type} (b : Kind)
    (gi : b = Kind.gaussian → I) (pj : b = Kind.physical → J)
    (hb : b = Kind.gaussian) :
    letter (⟨b, match (generalizing := false) h : b with
      | .gaussian => gi h
      | .coupling => PUnit.unit
      | .physical => pj h⟩ : Σ t, Label I J t) = Sum.inl (gi hb) := by
  cases hb
  rfl

private lemma letter_physical {I J : Type} (b : Kind)
    (gi : b = Kind.gaussian → I) (pj : b = Kind.physical → J)
    (hb : b = Kind.physical) :
    letter (⟨b, match (generalizing := false) h : b with
      | .gaussian => gi h
      | .coupling => PUnit.unit
      | .physical => pj h⟩ : Σ t, Label I J t) = Sum.inr (some (pj hb)) := by
  cases hb
  rfl

private lemma letter_coupling {I J : Type} (b : Kind)
    (gi : b = Kind.gaussian → I) (pj : b = Kind.physical → J)
    (hb : b = Kind.coupling) :
    letter (⟨b, match (generalizing := false) h : b with
      | .gaussian => gi h
      | .coupling => PUnit.unit
      | .physical => pj h⟩ : Σ t, Label I J t) = Sum.inr none := by
  cases hb
  rfl

private lemma decode_gaussian {I J : Type} {n : ℕ} (c : Choice I J n)
    (u : Internal c.1) : decode c u.val = Sum.inl (c.2.1 u) := by
  exact letter_gaussian (c.1 u.val)
    (fun h => c.2.1 ⟨u.val, h⟩) (fun h => c.2.2 ⟨u.val, h⟩) u.property

private lemma decode_physical {I J : Type} {n : ℕ} (c : Choice I J n)
    (u : External c.1) : decode c u.val = Sum.inr (some (c.2.2 u)) := by
  exact letter_physical (c.1 u.val)
    (fun h => c.2.1 ⟨u.val, h⟩) (fun h => c.2.2 ⟨u.val, h⟩) u.property

private lemma decode_coupling {I J : Type} {n : ℕ} (c : Choice I J n)
    (k : Fin n) (h : c.1 k = Kind.coupling) : decode c k = Sum.inr none := by
  exact letter_coupling (c.1 k)
    (fun h => c.2.1 ⟨k, h⟩) (fun h => c.2.2 ⟨k, h⟩) h

private lemma decode_left_iff {I J : Type} {n : ℕ} (c : Choice I J n)
    (k : Fin n) : (decode c k).isLeft ↔ c.1 k = Kind.gaussian := by
  cases h : c.1 k with
  | gaussian => simp [decode_gaussian c ⟨k, h⟩]
  | coupling => simp [decode_coupling c k h]
  | physical => simp [decode_physical c ⟨k, h⟩]

def gaussianEquiv {I J : Type} {n : ℕ} (c : Choice I J n) :
    Internal c.1 ≃ NativeTensorRows.GaussianSlot (decode c) where
  toFun u := ⟨u.val, (decode_left_iff c u.val).2 u.property⟩
  invFun u := ⟨u.val, (decode_left_iff c u.val).1 u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma gaussian_index {I J : Type} {n : ℕ} (c : Choice I J n)
    (u : Internal c.1) :
    NativeTensorRows.gaussianIndex (decode c) (gaussianEquiv c u) = c.2.1 u :=
  (Sum.getLeft_eq_iff _).2 (decode_gaussian c u)

private lemma gaussian_word {I J : Type} {n : ℕ} (c : Choice I J n) :
    Normal.glyphs c.2.1 univ =
      Normal.glyphs (NativeTensorRows.gaussianIndex (decode c)) univ := by
  exact Fintype.prod_equiv (gaussianEquiv c) _ _
    (fun u => congrArg MvPolynomial.X (gaussian_index c u).symm)

def physicalWeight {I J : Type} {n : ℕ} (B : J → ℝ) (c : Choice I J n) : ℂ :=
  ∏ u : External c.1, (B (c.2.2 u) : ℂ)

private lemma external_product {I J : Type} {n : ℕ} (B : J → ℝ)
    (c : Choice I J n) :
    NativeTensorRows.externalProduct B (decode c) = physicalWeight B c := by
  apply Finset.prod_congr_set {k : Fin n | c.1 k = Kind.physical}
    (fun k => NativeTensorRows.externalWeight B (decode c k))
    (fun k => (B (c.2.2 k) : ℂ))
  · intro k hk
    simp [decode_physical c ⟨k, hk⟩, NativeTensorRows.externalWeight]
  · intro k hk
    cases h : c.1 k with
    | gaussian => simp [decode_gaussian c ⟨k, h⟩, NativeTensorRows.externalWeight]
    | coupling => simp [decode_coupling c k h, NativeTensorRows.externalWeight]
    | physical => exact False.elim (hk h)

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (e : E) (L : (I → ℝ) →ₗ[ℝ] E) (M : (J → ℝ) →ₗ[ℝ] E)

def tensorValue {n : ℕ} (T : Tensor.T E ℂ n) (c : Choice I J n) : ℂ :=
  T (NativeTensorRows.direction e L M ∘ decode c)

def rows {n : ℕ} (B : J → ℝ) (T : Tensor.T E ℂ n) : Rows I where
  Choice := Choice I J n
  finiteChoice := inferInstance
  Leg c := Internal c.1
  finiteLeg _ := inferInstance
  coefficient c := tensorValue e L M T c * physicalWeight B c
  index c := c.2.1

/-- Exact wordL regrouping into fixed slot patterns, separate Gaussian
and physical labels, and the original ordered tensor value. -/
theorem word_rows {n : ℕ} (B : J → ℝ) (T : Tensor.T E ℂ n) :
    Assembly.wordL (e + M B) L T = (rows e L M B T).polynomial := by
  rw [NativeTensorRows.word_rows]
  unfold Rows.polynomial
  symm
  apply Fintype.sum_equiv (choiceEquiv n).symm
  intro c
  change (tensorValue e L M T c * physicalWeight B c) • Normal.glyphs c.2.1 univ =
    (T (NativeTensorRows.direction e L M ∘ (choiceEquiv n).symm c) *
      NativeTensorRows.externalProduct B ((choiceEquiv n).symm c)) •
        Normal.glyphs (NativeTensorRows.gaussianIndex ((choiceEquiv n).symm c)) univ
  simp only [choice_decode, external_product B c, gaussian_word c, tensorValue]
  rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem weight_zero {n : ℕ} (c : Choice I J n) (h : Nonempty (External c.1)) :
    physicalWeight (0 : J → ℝ) c = 0 := by
  obtain ⟨u⟩ := h
  exact Finset.prod_eq_zero (mem_univ u) rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem weight_empty {n : ℕ} (B : J → ℝ) (c : Choice I J n)
    (h : IsEmpty (External c.1)) : physicalWeight B c = 1 := by
  letI := h
  exact Finset.prod_eq_one (fun u _ => isEmptyElim u)

end YM.Integration.PatternTensorRows
end
