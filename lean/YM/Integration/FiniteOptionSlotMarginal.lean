import YM.Integration.PatternTensorRows
import YM.Integration.NativeMixedSlotProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# An anchored Option alphabet, grouped before summing field labels

The fixed some i0 slot remains a field slot. Each other position chooses
coupling or field once, giving exactly 2^k patterns. All field labels remain
summed within each pattern. The explicit permutation puts the field block
first, exactly as native Paths.prepend does. There is no alphabet-size factor.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FiniteOptionSlotMarginal

open Finset Function
open scoped BigOperators Classical

abbrev Field {K : Type} (p : K → Bool) := {k // p k = true}
abbrev Coupling {K : Type} (p : K → Bool) := {k // p k = false}

private def Label (I : Type) : Bool → Type
  | false => PUnit
  | true => I

private def letter {I : Type} : (Σ b, Label I b) ≃ Option I where
  toFun
    | ⟨false, _⟩ => none
    | ⟨true, i⟩ => some i
  invFun
    | none => ⟨false, PUnit.unit⟩
    | some i => ⟨true, i⟩
  left_inv z := by
    rcases z with ⟨b, i⟩
    cases b with
    | false => cases i; rfl
    | true => rfl
  right_inv z := by cases z <;> rfl

private def labelsOf {I K : Type} (p : K → Bool) (u : Field p → I) :
    ∀ k, Label I (p k) :=
  fun k => match h : p k with
  | false => PUnit.unit
  | true => u ⟨k, h⟩

private lemma bool_eta {I : Type} (b : Bool) (a : Label I b) :
    (show Label I b from match (generalizing := false) h : b with
    | false => PUnit.unit
    | true => cast (congrArg (Label I) h) a) = a := by
  cases b with
  | false => cases a; rfl
  | true => rfl

private lemma bool_field {I : Type} (b : Bool)
    (f : b = true → I) (hb : b = true) :
    cast (congrArg (Label I) hb)
      (show Label I b from match (generalizing := false) h : b with
      | false => PUnit.unit
      | true => f h) = f hb := by
  cases hb
  rfl

private def fieldCoordinates {I K : Type} (p : K → Bool) :
    (∀ k, Label I (p k)) ≃ (Field p → I) where
  toFun a u := cast (congrArg (Label I) u.property) (a u.val)
  invFun := labelsOf p
  left_inv a := by
    funext k
    exact bool_eta (p k) (a k)
  right_inv u := by
    funext k
    exact bool_field (p k.val) (fun h => u ⟨k.val, h⟩) k.property

private def choices {I K : Type} :
    (K → Option I) ≃ (Σ p : K → Bool, Field p → I) :=
  (Equiv.piCongrRight (fun _ => letter.symm)).trans
    (PatternTensorRows.piSigma.trans
      (Equiv.sigmaCongrRight (fun p => fieldCoordinates p)))

def decode {I K : Type} (p : K → Bool) (u : Field p → I) : K → Option I :=
  fun k => letter ⟨p k, labelsOf p u k⟩

private lemma letter_false {I : Type} (b : Bool)
    (f : b = true → I) (hb : b = false) :
    letter (⟨b, match (generalizing := false) h : b with
      | false => PUnit.unit
      | true => f h⟩ : Σ t, Label I t) = none := by
  cases hb
  rfl

private lemma letter_true {I : Type} (b : Bool)
    (f : b = true → I) (hb : b = true) :
    letter (⟨b, match (generalizing := false) h : b with
      | false => PUnit.unit
      | true => f h⟩ : Σ t, Label I t) = some (f hb) := by
  cases hb
  rfl

private lemma decode_false {I K : Type} (p : K → Bool) (u : Field p → I)
    (k : K) (hk : p k = false) : decode p u k = none :=
  letter_false (p k) (fun h => u ⟨k, h⟩) hk

private lemma decode_true {I K : Type} (p : K → Bool) (u : Field p → I)
    (k : K) (hk : p k = true) : decode p u k = some (u ⟨k, hk⟩) :=
  letter_true (p k) (fun h => u ⟨k, h⟩) hk

private lemma choices_decode {I K : Type} (z : Σ p : K → Bool, Field p → I) :
    (choices (I := I) (K := K)).symm z = decode z.1 z.2 := rfl

/-- Exact regrouping, retaining the complete field-label sum for each pattern. -/
theorem sum_patterns {I K : Type} [Fintype I] [Fintype K]
    (F : (K → Option I) → ℝ) :
    (∑ x : K → Option I, F x) =
      ∑ p : K → Bool, ∑ u : Field p → I, F (decode p u) := by
  have h := (choices (I := I) (K := K)).symm.sum_comp F
  simpa only [choices_decode, Fintype.sum_sigma] using h.symm

/-- Enumerating field positions changes no field-label sum. -/
theorem sum_pattern_fin {I K : Type} [Fintype I] [Fintype K]
    (p : K → Bool) (F : (K → Option I) → ℝ) :
    (∑ u : Field p → I, F (decode p u)) =
      ∑ q : Fin (Fintype.card (Field p)) → I,
        F (decode p (q ∘ Fintype.equivFin (Field p))) := by
  let e := Equiv.arrowCongr (Fintype.equivFin (Field p)) (Equiv.refl I)
  apply Fintype.sum_equiv e
  intro u
  simp [e, Equiv.arrowCongr, Function.comp_def]

private theorem patterns_bound {I K : Type} [Fintype I] [Fintype K]
    (F : (K → Option I) → ℝ) (A : ℝ)
    (h : ∀ p : K → Bool, (∑ u : Field p → I, F (decode p u)) ≤ A) :
    (∑ x : K → Option I, F x) ≤ (2 : ℝ) ^ Fintype.card K * A := by
  rw [sum_patterns]
  calc
    _ ≤ ∑ _p : K → Bool, A := Finset.sum_le_sum (fun p _ => h p)
    _ = _ := by simp

private def optionSplit {A B : Type} : Option (A ⊕ B) ≃ Option A ⊕ B where
  toFun
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  invFun
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  left_inv x := by rcases x with (_ | (a | b)) <;> rfl
  right_inv x := by rcases x with (_ | a) | b <;> rfl

/-- Native order: all d field positions, followed by the c coupling positions. -/
private def blockIndex (c : ℕ) : (d : ℕ) → Fin (c + d) ≃ Fin d ⊕ Fin c
  | 0 =>
    { toFun := Sum.inr
      invFun := Sum.elim Fin.elim0 id
      left_inv := fun _ => rfl
      right_inv := by
        intro x
        rcases x with i | i
        · exact Fin.elim0 i
        · rfl }
  | d + 1 =>
    (finSuccEquiv (c + d)).trans
      ((Equiv.optionCongr (blockIndex c d)).trans
        (optionSplit.trans
          (Equiv.sumCongr (finSuccEquiv d).symm (Equiv.refl (Fin c)))))

private lemma blockIndex_zero (c d : ℕ) :
    blockIndex c (d + 1) 0 = Sum.inl 0 := by
  simp [blockIndex, optionSplit, Equiv.optionCongr, Equiv.sumCongr]

private lemma blockIndex_succ (c d : ℕ) (i : Fin (c + d)) :
    blockIndex c (d + 1) i.succ =
      Sum.map Fin.succ id (blockIndex c d i) := by
  cases h : blockIndex c d i <;> simp [blockIndex, optionSplit, Equiv.optionCongr, Equiv.sumCongr, h]

private lemma prepend_index {E : Type} (c d : ℕ)
    (v : Fin c → E) (u : Fin d → E) (i : Fin (c + d)) :
    YM.Push.Loops.Paths.prepend v u i = Sum.elim u v (blockIndex c d i) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [YM.Push.Loops.Paths.prepend, Fin.cons_zero,
        blockIndex_zero, Sum.elim_inl]
    · change YM.Push.Loops.Paths.prepend v (Fin.tail u) i = _
      rw [ih, blockIndex_succ]
      cases blockIndex c d i <;> rfl

private def splitPositions {K : Type} (p : K → Bool) : K ≃ Field p ⊕ Coupling p where
  toFun k := match h : p k with
    | false => Sum.inr ⟨k, h⟩
    | true => Sum.inl ⟨k, h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv k := by dsimp only; split <;> rfl
  right_inv z := by
    rcases z with ⟨k, hk⟩ | ⟨k, hk⟩
    · dsimp only
      split
      · rename_i h
        exact False.elim (Bool.false_ne_true (h.symm.trans hk))
      · rfl
    · dsimp only
      split
      · rfl
      · rename_i h
        exact False.elim (Bool.false_ne_true (hk.symm.trans h))

private lemma splitPositions_false {K : Type} (p : K → Bool) (k : K)
    (hk : p k = false) : splitPositions p k = Sum.inr ⟨k, hk⟩ := by
  change (show Field p ⊕ Coupling p from match h : p k with
    | false => Sum.inr ⟨k, h⟩
    | true => Sum.inl ⟨k, h⟩) = _
  split
  · rfl
  · rename_i h
    exact False.elim (Bool.false_ne_true (hk.symm.trans h))

private lemma splitPositions_true {K : Type} (p : K → Bool) (k : K)
    (hk : p k = true) : splitPositions p k = Sum.inl ⟨k, hk⟩ := by
  change (show Field p ⊕ Coupling p from match h : p k with
    | false => Sum.inr ⟨k, h⟩
    | true => Sum.inl ⟨k, h⟩) = _
  split
  · rename_i h
    exact False.elim (Bool.false_ne_true (h.symm.trans hk))
  · rfl

def fieldCount {n : ℕ} (p : Fin n → Bool) : ℕ := Fintype.card (Field p)
def couplingCount {n : ℕ} (p : Fin n → Bool) : ℕ := Fintype.card (Coupling p)

/-- The anchor is the additional field position; no original position is removed. -/
theorem slot_count {n : ℕ} (p : Fin n → Bool) :
    couplingCount p + (fieldCount p + 1) = n + 1 := by
  have h := Fintype.card_congr (splitPositions p)
  simp only [Fintype.card_fin, Fintype.card_sum] at h
  unfold couplingCount fieldCount
  omega

private def ordered {n : ℕ} (p : Fin n → Bool) (j : Fin (n + 1)) :
    Fin (n + 1) ≃ Fin (fieldCount p + 1) ⊕ Fin (couplingCount p) :=
  (finSuccEquiv' j).trans
    ((Equiv.optionCongr (splitPositions p)).trans
      (optionSplit.trans
        (Equiv.sumCongr
          ((Equiv.optionCongr (Fintype.equivFin (Field p))).trans
            (finSuccEquiv (fieldCount p)).symm)
          (Fintype.equivFin (Coupling p)))))

/-- A permutation of the unchanged total count, depending only on the slot pattern. -/
def blockPermutation {n : ℕ} (p : Fin n → Bool) (j : Fin (n + 1)) :
    Equiv.Perm (Fin (couplingCount p + (fieldCount p + 1))) :=
  (finCongr (slot_count p)).trans
    ((ordered p j).trans (blockIndex (couplingCount p) (fieldCount p + 1)).symm)

private lemma blockPermutation_index {n : ℕ} (p : Fin n → Bool)
    (j : Fin (n + 1)) (t : Fin (n + 1)) :
    blockIndex (couplingCount p) (fieldCount p + 1)
      (blockPermutation p j (Fin.cast (slot_count p).symm t)) = ordered p j t := by
  change blockIndex (couplingCount p) (fieldCount p + 1)
    ((blockIndex (couplingCount p) (fieldCount p + 1)).symm
      (ordered p j (Fin.cast (slot_count p) (Fin.cast (slot_count p).symm t)))) = _
  simp

/-- Exact field-first block, with the anchor retained at its original physical slot. -/
theorem pattern_slots {I : Type} {n : ℕ} (p : Fin n → Bool)
    (j : Fin (n + 1)) (i0 : I) (q : Fin (fieldCount p) → I) :
    Fin.insertNth (α := fun _ => Option I) j (some i0) (decode p (q ∘ Fintype.equivFin (Field p))) =
      fun t => YM.Push.Loops.Paths.prepend
        (fun _ : Fin (couplingCount p) => (none : Option I))
        (fun u => some (Fin.cons (α := fun _ => I) i0 q u))
        (blockPermutation p j (Fin.cast (slot_count p).symm t)) := by
  funext t
  rw [prepend_index, blockPermutation_index]
  refine Fin.succAboveCases j ?_ (fun k => ?_) t
  · simp [ordered, optionSplit, Equiv.optionCongr, Equiv.sumCongr]
    exact (congrArg (Fin.cons (α := fun _ => I) i0 q)
      (finSuccEquiv_symm_none (n := fieldCount p))).symm
  · rw [Fin.insertNth_apply_succAbove]
    cases h : p k with
    | false =>
      rw [decode_false p _ k h]
      simp [ordered, splitPositions_false p k h, optionSplit, Equiv.optionCongr,
        Equiv.sumCongr]
    | true =>
      rw [decode_true p _ k h]
      simp [ordered, splitPositions_true p k h, optionSplit, Equiv.optionCongr,
        Equiv.sumCongr]
      exact (congrArg (Fin.cons (α := fun _ => I) i0 q)
        (finSuccEquiv_symm_some ((Fintype.equivFin (Field p)) ⟨k, h⟩))).symm

/-- Use each mixed-pattern bound before summing the 2^n distinct patterns. -/
theorem anchored_mixed_bound {I : Type} [Fintype I] {n : ℕ}
    (F : (Fin (n + 1) → Option I) → ℝ) (j : Fin (n + 1)) (i0 : I) (A : ℝ)
    (hF : ∀ (c d : ℕ) (h : c + (d + 1) = n + 1)
      (σ : Equiv.Perm (Fin (c + (d + 1)))),
      (∑ q : Fin d → I, F (fun t => YM.Push.Loops.Paths.prepend
        (fun _ : Fin c => (none : Option I))
        (fun u => some (Fin.cons (α := fun _ => I) i0 q u)) (σ (Fin.cast h.symm t)))) ≤ A) :
    (∑ x : Fin n → Option I, F (Fin.insertNth (α := fun _ => Option I) j (some i0) x)) ≤ (2 : ℝ)^n * A := by
  suffices h : (∑ x : Fin n → Option I, F (Fin.insertNth (α := fun _ => Option I) j (some i0) x)) ≤
      (2 : ℝ) ^ Fintype.card (Fin n) * A by
    simpa only [Fintype.card_fin] using h
  have hp : ∀ p : Fin n → Bool,
      (∑ u : Field p → I,
        F (Fin.insertNth (α := fun _ => Option I) j (some i0) (decode p u))) ≤ A := by
    intro p
    calc
      (∑ u : Field p → I, F (Fin.insertNth (α := fun _ => Option I) j (some i0) (decode p u))) =
          ∑ q : Fin (fieldCount p) → I,
            F (Fin.insertNth (α := fun _ => Option I) j (some i0)
              (decode p (q ∘ Fintype.equivFin (Field p)))) :=
        by
          convert sum_pattern_fin p
            (fun x => F (Fin.insertNth (α := fun _ => Option I) j (some i0) x)) using 1
          all_goals
            apply Finset.sum_congr
            · exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
            · intro u _; rfl
      _ = ∑ q : Fin (fieldCount p) → I, F (fun t => YM.Push.Loops.Paths.prepend
          (fun _ : Fin (couplingCount p) => (none : Option I))
          (fun u => some (Fin.cons (α := fun _ => I) i0 q u))
          (blockPermutation p j (Fin.cast (slot_count p).symm t))) := by
        apply Finset.sum_congr rfl
        intro q _
        exact congrArg F (pattern_slots p j i0 q)
      _ ≤ A := hF (couplingCount p) (fieldCount p) (slot_count p) (blockPermutation p j)
  convert patterns_bound
    (fun x => F (Fin.insertNth (α := fun _ => Option I) j (some i0) x)) A
    (by
      intro p
      convert hp p using 1
      apply Finset.sum_congr
      · exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
      · intro u _; rfl) using 1
  apply Finset.sum_congr
  · exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  · intro x _; rfl

def direction {I E : Type} [Zero E] (v : I → E) : Option I → ℝ × E
  | none => (1, 0)
  | some i => (0, v i)

/-- The block is literally the native tuple, with coupling direction one. -/
theorem direction_prepend {I E : Type} [NormedAddCommGroup E] (v : I → E)
    (c d : ℕ) (q : Fin d → I) (t : Fin (c + d)) :
    direction v (YM.Push.Loops.Paths.prepend
      (fun _ : Fin c => (none : Option I)) (fun i => some (q i)) t) =
      NativeMixedSlotProduct.slots c (fun i => v (q i)) t := by
  unfold NativeMixedSlotProduct.slots
  rw [prepend_index, prepend_index]
  cases blockIndex c d t <;> rfl

/-- Direct inlet for a norm or any real functional of the original ordered tensor. -/
theorem anchored_direction_bound {I E : Type} [Fintype I] [NormedAddCommGroup E] {n : ℕ}
    (T : (Fin (n + 1) → ℝ × E) → ℝ) (v : I → E)
    (j : Fin (n + 1)) (i0 : I) (A : ℝ)
    (hT : ∀ (c d : ℕ) (h : c + (d + 1) = n + 1)
      (σ : Equiv.Perm (Fin (c + (d + 1)))),
      (∑ q : Fin d → I, T (fun t => NativeMixedSlotProduct.slots c
        (fun u => v (Fin.cons (α := fun _ => I) i0 q u)) (σ (Fin.cast h.symm t)))) ≤ A) :
    (∑ x : Fin n → Option I,
      T (fun t => direction v (Fin.insertNth (α := fun _ => Option I) j (some i0) x t))) ≤ (2 : ℝ)^n * A := by
  apply anchored_mixed_bound (fun x => T (fun t => direction v (x t))) j i0 A
  intro c d h σ
  simpa only [direction_prepend] using hT c d h σ

end YM.Integration.FiniteOptionSlotMarginal
end
