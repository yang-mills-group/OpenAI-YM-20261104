import YM.WilsonMS.Top.Stokes
import YM.WilsonMS.Top.ClosedSeries

/-! # Specialization of field slots (including the Wick calculation)

This is `MS.Cylinder.shade` on finite alphabets. Mnemonic:
`T a b` is the coefficient used in replacing letter `a` by using `b`.
Push propagators the opposite way. -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS
open MS MS.Koszul MS.Cylinder MS.Book MS.Swirl MS.Orbit MS.Orbit.Cog Finset Matrix

variable {A B C : Type} [Fintype A] (T : Matrix A B ℂ) {p : Sector A} {q : Sector B}

def specialize : Raw A ℂ →ₗ[ℂ] Raw B ℂ :=
  lantern Finset.univ Tᵀ

lemma specialize_nil (F : Raw A ℂ) : specialize T F [] = F [] :=
  rfl

lemma specialize_deriv (j : B) (F : Raw A ℂ) :
    D j (specialize T F) = ∑ i : A, T i j • specialize T (D i F) :=
  lantern_drop ..

lemma specialize_shade (F : Cyl A ℂ) : specialize T F.val = shade Tᵀ F :=
  (tinted Tᵀ F (s := Finset.univ)
      (by
        rw [coe_univ]
        exact Uses.entire _)).symm

lemma specialize_mask (h : ℤ) (F : Raw A ℂ) : specialize T (mask h F) = mask h (specialize T F) := by
  let K : Cyl A ℂ := region.symm F
  change specialize T (model h K).val = mask h (specialize T K.val)
  rw [specialize_shade, specialize_shade, mod_ink]

lemma specialize_coin (x : ℂ) : specialize T (coin x) = coin x :=
  (specialize_shade T (piece x)).trans (coin_turn ..)

lemma specialize_limit {h : ℤ} {F : Raw A ℂ} (hf : Limit F h) : Limit (specialize T F) h := by
  let K : Cyl A ℂ := region.symm F
  change Limit (specialize T K.val) h
  rw [specialize_shade]
  exact Limit.shades K hf _

lemma specialize_rank {h : ℤ} {F : Raw A ℂ} (hr : Book.rank h F) : Book.rank h (specialize T F) := by
  rw [rank_hat, ← specialize_mask, (rank_hat h).mp hr]

lemma specialize_single (i : A) (j : B) : specialize T (atLetter i) [j] = T i j := by
  rw [show specialize T (atLetter i) = _ from specialize_shade T (Cylinder.single i), name]
  rfl

lemma specialize_letter [Fintype B] (i : A) :
    specialize T (atLetter i) = ∑ j : B, T i j • atLetter j := by
  have hr : Book.rank 1 (specialize T (atLetter i)) := specialize_rank _ (Rails.letter i)
  rw [one_leg _ hr]
  simp_rw [specialize_single]

lemma specialize_identity [DecidableEq A] (F : Raw A ℂ) : specialize (1 : Matrix A A ℂ) F = F := by
  ext l
  induction l generalizing F with
  | nil => rfl
  | cons i l ih =>
    rw [D_eval i (specialize _ _), specialize_deriv]
    rw [Finset.sum_eq_single_of_mem i (mem_univ i), Matrix.one_apply_eq, one_smul]
    exact ih _
    intro c _ hc
    rw [Matrix.one_apply_ne hc, zero_smul]

variable {T} in
lemma specialize_tether (H : Tie p q Tᵀ) : Puff.Tether (specialize T) (Puff.actor p) (Puff.actor q) := by
  refine ⟨specialize_coin T 1, fun a b => ?_⟩
  let X : Cyl A ℂ := region.symm a
  let Y : Cyl A ℂ := region.symm b
  change specialize T (couple p X Y).val = product q (specialize T X.val) (specialize T Y.val)
  rw [specialize_shade, specialize_shade, specialize_shade]
  exact H.prod ..

variable {T} in
lemma specialize_symmetric (ht : Tie p q Tᵀ) {F : Raw A ℂ} (h : Symm p F) : Symm q (specialize T F) := by
  let K : Cyl A ℂ := region.symm F
  change Symm q (specialize T K.val)
  rw [specialize_shade]
  exact ht.sym _ h

variable [Fintype B]

lemma specialize_comp (U : Matrix B C ℂ) (F : Raw A ℂ) :
    specialize U (specialize T F) = specialize (T * U) F := by
  ext l
  induction l generalizing F with
  | nil => rfl
  | cons i l ih =>
    simp only [D_eval i (specialize _ _), specialize_deriv, map_sum, map_smul]
    simp_rw [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, Finset.sum_apply, Pi.smul_apply, ih]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [mul_smul, smul_comm]

/-- Congruence (not Hermitian conjugation) for the Wick lines. -/
def induce (K : Grain B) : Grain A :=
  (T * Matrix.of K * Tᵀ :)

omit [Fintype A] in
lemma induce_value (K : Grain B) (i j : A) :
    induce T K i j = ∑ y : B, ∑ x : B, T i x * K x y * T j y := by
  unfold induce
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Matrix.mul_apply, sum_mul]
  rfl

lemma frame_specialize (F : Raw A ℂ) (K : Grain B) :
    frame K (specialize T F) = specialize T (frame (induce T K) F) := by
  rw [fpΩ, fpΩ]
  simp_rw [map_sum, diffPair_apply, specialize_deriv, map_sum, map_smul, specialize_deriv,
    induce_value, Finset.smul_sum, Finset.sum_smul]
  let f (i j : B) (x y : A) := (T x i * K i j * T y j) • specialize T (D y (D x F))
  simp_rw [show ∀ i j x y, K i j • T x i • T y j • specialize T (D y (D x F)) = f i j x y from
      fun i j x y => by
      unfold f
      simp_rw [mul_smul, smul_comm (K i j) (T x i)]]
  change
    (∑ i : B, ∑ j : B, ∑ x : A, ∑ y : A, f i j x y) = ∑ x : A, ∑ y : A, ∑ j : B, ∑ i : B, f i j x y
  rw [Finset.sum_comm]
  simp_rw [show ∀ j : B, (∑ i : B, ∑ x : A, ∑ y : A, f i j x y) = ∑ x : A, ∑ y : A, ∑ i : B, f i j x y
      from fun j => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma wick_natural (K : Grain B) {F : Raw A ℂ} (hf : F ∈ Mini A) :
    View K (specialize T F) = View (induce T K) F := by
  obtain ⟨n, hn⟩ := hf
  have he (i : ℕ) : tep K i (specialize T F) = specialize T (tep (induce T K) i F) := by
    induction i with
    | zero =>
      rw [rise, rise]
      rfl
    | succ i ih => rw [teen, ih, teen, map_smul, frame_specialize]
  change Shot K (specialize T F) [] = Shot (induce T K) F []
  rw [dawn K (specialize_limit T hn), dawn _ hn]
  unfold effect
  simp_rw [LinearMap.sum_apply, he, ← map_sum, specialize_nil]
end YM.WilsonMS
