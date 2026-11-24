import YM.Integration.FiniteConnectedProgram
import YM.Comparison.RG02.Valence.Amplify

/-!
# Ordered tensor rows with explicit physical external indices

The alphabet is the disjoint union of original Gaussian indices and
Option physical indices. None is the coupling direction, evaluated at
one. Some j is the original physical coordinate B j. No basis of the
ambient joint space is selected: the full tensor is evaluated on the
supplied coupling, physical and Gaussian linear directions.

The polynomial identity below retains every ordered assignment and the
literal normalized tensor. It applies equally to marked kernelJet rows
and the signed order-(j+2) naked vacuum rows.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeTensorRows

open Finset Function
open YM.Marker YM.Multi YM.Next.Rank
open YM.Comparison.RG02
open YM.Comparison.RG02.Cumulants
open YM.Integration.FiniteConnectedProgram
open scoped BigOperators ContDiff Classical

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (e : E) (L : (I → ℝ) →ₗ[ℝ] E) (M : (J → ℝ) →ₗ[ℝ] E)

abbrev Alphabet (I J : Type) := I ⊕ Option J

def direction : Alphabet I J → E :=
  Sum.elim (fun i => L (Pi.single i 1))
    (fun o => o.elim e (fun j => M (Pi.single j 1)))

def value (B : J → ℝ) (z : I → ℝ) : Alphabet I J → ℝ :=
  Sum.elim z (fun o => o.elim 1 B)

def externalWeight (B : J → ℝ) : Alphabet I J → ℂ :=
  Sum.elim (fun _ => 1) (fun o => o.elim 1 (fun j => (B j : ℂ)))

def gaussianFactor : Alphabet I J → Normal.poly I :=
  Sum.elim MvPolynomial.X (fun _ => 1)

def coordinate (B : J → ℝ) : Alphabet I J → Normal.poly I :=
  Sum.elim MvPolynomial.X
    (fun o => o.elim 1 (fun j => MvPolynomial.C (B j : ℂ)))

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private lemma coordinate_factor (B : J → ℝ) (a : Alphabet I J) :
    coordinate B a =
      MvPolynomial.C (externalWeight B a) * gaussianFactor a := by
  rcases a with i | (_ | j)
  all_goals simp [coordinate, externalWeight, gaussianFactor]

private lemma coordinate_sum {K : Type} [Fintype K] [DecidableEq K] (z : K → ℝ) :
    (∑ i, z i • Pi.single i 1) = z := by
  ext i
  rw [Finset.sum_apply]
  simp [Pi.single_apply]

private lemma frame_sum (B : J → ℝ) (z : I → ℝ) :
    Assembly.translate (e + M B) L z =
      ∑ i, value B z i • direction e L M i := by
  rw [Fintype.sum_sum_type, Fintype.sum_option]
  simp only [value, direction, Sum.elim_inl, Sum.elim_inr,
    Option.elim_none, Option.elim_some, one_smul]
  simp_rw [← map_smul L, ← map_smul M]
  rw [← map_sum L, ← map_sum M, coordinate_sum, coordinate_sum]
  unfold Assembly.translate
  ac_rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private lemma coordinate_reading (B : J → ℝ) (z : I → ℝ)
    (a : Alphabet I J) :
    Cloud.paint z (coordinate B a) = Complex.ofReal (value B z a) := by
  rcases a with i | (_ | j)
  all_goals simp [coordinate, value, Cloud.paint]

def frameWord {n : ℕ}
    (B : J → ℝ) (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :
    Normal.poly I :=
  ∑ a : Fin n → Alphabet I J,
    MvPolynomial.C (T (direction e L M ∘ a)) *
      ∏ k, coordinate B (a k)

private lemma frame_reading {n : ℕ} (B : J → ℝ) (z : I → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :
    Cloud.paint z (frameWord e L M B T) =
      T (fun _ => Assembly.translate (e + M B) L z) := by
  simp_rw [frameWord, _root_.map_sum, _root_.map_mul, _root_.map_prod,
    show ∀ c : ℂ, Cloud.paint z (MvPolynomial.C c) = c from
      fun c => MvPolynomial.aeval_C .., coordinate_reading, frame_sum e L M B z]
  rw [T.map_sum_finset (fun _ i => _) (fun _ => Finset.univ),
    Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro a _
  simp only [T.map_smul_univ, Complex.real_smul, Complex.ofReal_prod, mul_comm,
    Function.comp_def]

abbrev GaussianSlot {n : ℕ} (a : Fin n → Alphabet I J) :=
  {k : Fin n // (a k).isLeft}

def gaussianIndex {n : ℕ} (a : Fin n → Alphabet I J)
    (k : GaussianSlot a) : I :=
  (a k.val).getLeft k.property

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private lemma gaussian_product {n : ℕ} (a : Fin n → Alphabet I J) :
    (∏ k, gaussianFactor (a k)) = Normal.glyphs (gaussianIndex a) univ := by
  apply Finset.prod_congr_set {k : Fin n | (a k).isLeft}
    (fun k => gaussianFactor (a k)) (fun k => MvPolynomial.X (gaussianIndex a k))
  · intro k hk
    exact congrArg gaussianFactor (Sum.inl_getLeft (a k) hk).symm
  · intro k hk
    cases ha : a k with
    | inl i => simp [ha] at hk
    | inr j => rfl

def externalProduct {n : ℕ} (B : J → ℝ) (a : Fin n → Alphabet I J) : ℂ :=
  ∏ k, externalWeight B (a k)

def rows {n : ℕ} (B : J → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) : Rows I where
  Choice := Fin n → Alphabet I J
  finiteChoice := inferInstance
  Leg := GaussianSlot
  finiteLeg _ := inferInstance
  coefficient a := T (direction e L M ∘ a) * externalProduct B a
  index := gaussianIndex

private lemma term_rows {n : ℕ} (B : J → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ)
    (a : Fin n → Alphabet I J) :
    MvPolynomial.C (T (direction e L M ∘ a)) *
        (∏ k, coordinate B (a k)) =
      (rows e L M B T).coefficient a • Normal.glyphs (gaussianIndex a) univ := by
  simp_rw [coordinate_factor]
  rw [Finset.prod_mul_distrib, ← map_prod, gaussian_product]
  simp only [rows, externalProduct]
  rw [← mul_assoc, ← map_mul, MvPolynomial.C_mul']

/-- Exact wordL expansion. The physical and Gaussian alphabets remain disjoint. -/
theorem word_rows {n : ℕ} (B : J → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :
    Assembly.wordL (e + M B) L T = (rows e L M B T).polynomial := by
  have hw : Assembly.wordL (e + M B) L T = frameWord e L M B T :=
    Valence.Enlist.paint_inj (fun z =>
      (Assembly.reading_word (e + M B) L z T).trans
        (frame_reading e L M B z T).symm)
  rw [hw]
  unfold frameWord Rows.polynomial
  exact Finset.sum_congr rfl (fun a _ => term_rows e L M B T a)

/-- A physical slot is distinct from both the coupling direction and a
Gaussian slot, even when their eventual numeric coordinates agree. -/
def HasExternal {n : ℕ} (a : Fin n → Alphabet I J) : Prop :=
  ∃ k j, a k = Sum.inr (some j)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem external_zero {n : ℕ} (a : Fin n → Alphabet I J) (h : HasExternal a) :
    externalProduct (0 : J → ℝ) a = 0 := by
  obtain ⟨k, j, hk⟩ := h
  unfold externalProduct
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hk, externalWeight]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem external_absent {n : ℕ} (B : J → ℝ) (a : Fin n → Alphabet I J)
    (h : ¬ HasExternal a) : externalProduct B a = 1 := by
  unfold externalProduct
  apply Finset.prod_eq_one
  intro k _
  cases hk : a k with
  | inl i => rfl
  | inr j =>
    cases j with
    | none => rfl
    | some j => exact False.elim (h ⟨k, j, hk⟩)

/-- Subtracting the value at B=0 removes exactly the assignments with no
physical external slot. The coupling-at-one assignments are retained
until this explicit subtraction. -/
theorem coefficient_centered {n : ℕ} (B : J → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ)
    (a : Fin n → Alphabet I J) :
    (rows e L M B T).coefficient a - (rows e L M 0 T).coefficient a =
      if HasExternal a then (rows e L M B T).coefficient a else 0 := by
  by_cases h : HasExternal a
  · rw [if_pos h]
    change _ - (T (direction e L M ∘ a) * externalProduct 0 a) = _
    rw [external_zero a h, mul_zero, sub_zero]
  · rw [if_neg h]
    change T (direction e L M ∘ a) * externalProduct B a -
      T (direction e L M ∘ a) * externalProduct 0 a = 0
    rw [external_absent B a h, external_absent 0 a h, sub_self]

end YM.Integration.NativeTensorRows
end
