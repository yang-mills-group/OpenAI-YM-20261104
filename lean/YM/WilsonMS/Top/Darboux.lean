import YM.WilsonMS.Top.Stokes

/-!
# Root ghost block: linear algebra of admissible gauge slices

Letter conventions for our finite Wilson comparison. `symbol` uses negative
Hessian on A fields (exponential coefficient); `R` is the derivative of the
gauge transformations. `C` is the Gaussian covariance, singular examples
allowed. `L` is a left inverse of R (choose for instance tree, or Landau
slice). `Splitting` is the propagator criterion: `C * H + R * L = 1`. In
particular with `L * C = 0` this says to use the inverse on the slice;
there are also soft versions (see `SoftCondition.lean`).

Verify by matrix calculation that the BV operator formed from the quadratic
exponent contracts using this data. A second such calculation shows the Wick
valuation kills the free quantum differential. These two things imply agreement
of insertions on the different, possibly singular, gauge slices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Darboux
open MS MS.Koszul MS.Cylinder MS.Book MS.Swirl MS.Orbit MS.Orbit.Cog
open Finset Matrix

variable {E U T : Type}

abbrev Letters (E U : Type) :=
  (E ⊕ U) ⊕ (E ⊕ U)

abbrev a (i : E) : Letters E U :=
  .inl (.inl i)

abbrev k (i : E) : Letters E U :=
  .inr (.inl i)

abbrev c (j : U) : Letters E U :=
  .inl (.inr j)

abbrev b (j : U) : Letters E U :=
  .inr (.inr j)

def parity : Sector (Letters E U)
  | .inl (.inl _) | .inr (.inr _) => false
  | .inl (.inr _) | .inr (.inl _) => true

def ports (E U : Type) : Bonded (parity (E := E) (U := U)) (E ⊕ U)
    where
  plain := ⟨Sum.inl, Sum.inl_injective⟩
  dual := ⟨Sum.inr, Sum.inr_injective⟩
  diff i j := Sum.inl_ne_inr
  wave i := by cases i <;> rfl

section
variable {H : Matrix E E ℂ} {R : Matrix E U ℂ}

/-- Hessian entries of the scaled exponent `S`. `R` is the derivative
at zero: columns with *based* site gauge index, rows link indices.
See `MS.Wilson.Gauge` for the infinitesimal-sign convention.
-/
def symbol (H : Matrix E E ℂ) (R : Matrix E U ℂ) : Matrix (Letters E U) (Letters E U) ℂ
  | .inl (.inl i), .inl (.inl j) => -H i j
  | .inr (.inl i), .inl (.inr j) => R i j
  | .inl (.inr j), .inr (.inl i) => -R i j
  | _, _ => 0

variable [Fintype E] [Fintype U] {S : Raw (Letters E U) ℂ} (h : WilsonMS.Quadratic (ports E U) S)
  (he : ∀ i j : Letters E U, S [i, j] = symbol H R i j)

include h

lemma plain (i : E ⊕ U) :
    classicalD (ports E U) S (atLetter (Sum.inl i)) = ((ports E U).fee i : ℂ) • D (Sum.inr i) S := by
  classical
  let X : Letters E U := Sum.inl i
  rw [classical_apply, Bonded.by_lap _ h.even, Finset.sum_eq_single_of_mem i (mem_univ _)]
  · rw [show D ((ports E U).plain i) (atLetter X (R := ℂ)) = coin 1 from hear X, ←
      (coin_pure 1).central, coin_product, one_smul,
      unheard _ (show (ports E U).dual i ≠ X from Ne.symm ((ports E U).diff i i)), map_zero, add_zero]
    rfl
  intro j _ hj
  have hf : (ports E U).plain i = X := rfl
  rw [unheard _
      (show (ports E U).plain j ≠ X from fun he =>
        hj ((ports E U).plain.injective (he.trans hf.symm))),
    unheard _ (show (ports E U).dual j ≠ X from Ne.symm ((ports E U).diff i j))]
  simp

lemma dual (i : E ⊕ U) :
    classicalD (ports E U) S (atLetter (Sum.inr i)) = ((ports E U).fee i : ℂ) • D (Sum.inl i) S := by
  classical
  let X : Letters E U := Sum.inr i
  rw [classical_apply, Bonded.by_lap _ h.even, Finset.sum_eq_single_of_mem i (mem_univ _)]
  · rw [show D ((ports E U).dual i) (atLetter X (R := ℂ)) = coin 1 from hear X, ←
      (coin_pure 1).central, coin_product, one_smul,
      unheard _ (show (ports E U).plain i ≠ X from (ports E U).diff i i), map_zero, zero_add]
    rfl
  intro j _ hj
  have hf : (ports E U).dual i = X := rfl
  rw [unheard _
      (show (ports E U).dual j ≠ X from fun he => hj ((ports E U).dual.injective (he.trans hf.symm))),
    unheard _ (show (ports E U).plain j ≠ X from (ports E U).diff j i)]
  simp

include he

/-- Free differential in our coordinates. -/
lemma leg_a (i : E) : classicalD (ports E U) S (atLetter (a i)) = ∑ j : U, R i j • atLetter (c j) := by
  classical
  change letterD (ports E U) S (a i) = _
  nth_rw 1 [one_leg _ (h.promotesField.rank _)]
  have hh : letterD (ports E U) S (a i) = D (k i) S := (plain h _).trans (one_smul ℂ _)
  simp_rw [hh, at_D, he]
  simp [Fintype.sum_sum_type, Letters, symbol, k, c]

lemma leg_k (i : E) :
    classicalD (ports E U) S (atLetter (k i)) = ∑ j : E, (-H i j) • atLetter (a j) := by
  classical
  change letterD (ports E U) S (k i) = _
  nth_rw 1 [one_leg _ (h.promotesField.rank _)]
  have hh : letterD (ports E U) S (k i) = D (a i) S := (dual h _).trans (one_smul ℂ _)
  simp_rw [hh, at_D, he]
  simp [Fintype.sum_sum_type, Letters, symbol, a]

lemma leg_c (j : U) : classicalD (ports E U) S (atLetter (c j)) = 0 := by
  classical
  change letterD (ports E U) S (c j) = _
  nth_rw 1 [one_leg _ (h.promotesField.rank _)]
  have hh : letterD (ports E U) S (c j) = -(D (b j) S) := (plain h _).trans (neg_one_smul ℂ _)
  simp_rw [hh, Pi.neg_apply, at_D, he]
  simp [Letters, symbol]

lemma leg_b (i : U) : classicalD (ports E U) S (atLetter (b i)) = ∑ j : E, R j i • atLetter (k j) := by
  classical
  change letterD (ports E U) S (b i) = _
  nth_rw 1 [one_leg _ (h.promotesField.rank _)]
  have hh : letterD (ports E U) S (b i) = -(D (c i) S) := (dual h _).trans (neg_one_smul ℂ _)
  simp_rw [hh, Pi.neg_apply, at_D, he]
  simp [Fintype.sum_sum_type, Letters, symbol, k, c]

end

def covariance (C : Matrix E E ℂ) (L : Matrix U E ℂ) : Grain (Letters E U)
  | .inl (.inl i), .inl (.inl j) => C i j
  | .inl (.inr i), .inr (.inl j) => -L i j
  | .inr (.inl j), .inl (.inr i) => L i j
  | _, _ => 0

def propagator (C : Matrix E E ℂ) (L : Matrix U E ℂ) : Grain (Letters E U) :=
  (2 : ℂ)⁻¹ • covariance C L

variable {H C : Matrix E E ℂ} {R : Matrix E U ℂ} {L : Matrix U E ℂ}

lemma correlation (i j : Letters E U) : Chill (propagator C L) i j = covariance C L i j := by
  simp [Chill, propagator]

lemma clear : Clear parity (propagator C L) := by
  rintro ((i | i) | (i | i)) ((j | j) | (j | j)) <;> simp [propagator, parity, covariance]

lemma propSym (hc : Cᵀ = C) : Cog.Sym parity (propagator C L) := by
  have he i j : C i j = C j i := congr_fun (congr_fun hc j) i
  rintro ((i | i) | (i | i)) ((j | j) | (j | j)) <;> simp [propagator, parity, covariance]
  exact he ..

section st
variable [Fintype E] [Fintype U] [DecidableEq E] [DecidableEq U]

/-- Conditions on the propagators. Need `H*C = I - (R*L)ᵀ`, not `= I`. -/
structure Splitting (H : Matrix E E ℂ) (R : Matrix E U ℂ) (C : Matrix E E ℂ) (L : Matrix U E ℂ) :
    Prop where
  symmC : Cᵀ = C
  symmH : Hᵀ = H
  left : L * R = 1
  inverse : C * H + R * L = 1

variable {S : Raw (Letters E U) ℂ} (h : WilsonMS.Quadratic (ports E U) S)
  (he : ∀ i j : Letters E U, S [i, j] = symbol H R i j) (hc : Splitting H R C L)

lemma Splitting.transposeLeft (X : Splitting H R C L) : Rᵀ * Lᵀ = 1 := by
  rw [← transpose_mul, X.left, transpose_one]

lemma Splitting.transposeRight (X : Splitting H R C L) : H * C + Lᵀ * Rᵀ = 1 := by
  simpa only [transpose_add, transpose_mul, X.symmC, X.symmH, transpose_one] using
    congr_arg transpose X.inverse

def vector (C : Matrix E E ℂ) (L : Matrix U E ℂ) : Letters E U → Raw (Letters E U) ℂ
  | .inl (.inl i) => ∑ j : E, (-C i j) • atLetter (k j)
  | .inl (.inr i) => ∑ j : E, L i j • atLetter (a j)
  | .inr (.inl i) => ∑ j : U, L j i • atLetter (b j)
  | _ => 0

omit [DecidableEq E] [DecidableEq U] in
lemma vectorOdd : OddField parity (vector C L)
    where
  rank
    i := by
    rcases i with (i | j) | (i | j)
    all_goals
      first
      | exact Rails.zero
      | exact Rails.sum _ (fun _ _ => Rails.smul _ (Rails.letter _))
  odd
    i := by
    rcases i with (i | j) | (i | j)
    · exact Pure.sum _ (fun x _ => Pure.smul _ (speaks_p (p := parity (E := E) (U := U)) (k x)))
    · exact Pure.sum _ (fun x _ => Pure.smul _ (speaks_p (p := parity (E := E) (U := U)) (a x)))
    · exact Pure.sum _ (fun x _ => Pure.smul _ (speaks_p (p := parity (E := E) (U := U)) (b x)))
    exact Pure.zero

omit [Fintype U] [DecidableEq E] [DecidableEq U] in
lemma mul_line {A X : Type} [Fintype X] (K : Matrix U E ℂ) (L : Matrix E X ℂ) (i : U) (f : X → A) :
    (∑ j : E, K i j • ∑ k : X, L j k • atLetter (R := ℂ) (f k)) =
      ∑ j : X, (K * L) i j • atLetter (f j) := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_apply, Finset.sum_smul]

lemma plus_line (M N : Matrix E E ℂ) (i : E) (f : E → T) (h : M + N = 1) :
    (∑ j : E, M i j • atLetter (R := ℂ) (f j)) + ∑ j : E, N i j • atLetter (f j) = atLetter (f i) := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_smul,
    show ∀ j : E, M i j + N i j = (1 : Matrix E E ℂ) i j from fun j => congr_fun (congr_fun h i) j]
  simp [Matrix.one_apply]

include h he hc in
lemma contraction : Contraction (vector C L) (ports E U) S
    where
  form := vectorOdd
  contracts
    i := by
    rcases i with (i | i) | (i | i)
    · unfold letterD
      change _ + vectorField parity _ (classicalD (ports E U) S (atLetter (a i))) = _
      simp_rw [leg_a h he, vector, map_sum, map_smul, vectorField_letter, leg_k h he, c, vector]
      rw [show (∑ j : E, (-C i j) • ∑ k : E, (-H j k) • atLetter (R := ℂ) (a (U := U) k)) = _ from
          mul_line (E := E) (U := E) (-C) (-H) i _,
        neg_mul_neg, mul_line R L i]
      exact plus_line _ _ _ _ hc.inverse
    · unfold letterD
      change _ + vectorField parity _ (classicalD (ports E U) S (atLetter (c i))) = _
      rw [leg_c h he, map_zero, add_zero]
      simp_rw [vector, map_sum, map_smul, leg_a h he]
      rw [mul_line L R i, hc.left]
      simp [c, Matrix.one_apply]
    · unfold letterD
      change _ + vectorField parity _ (classicalD (ports E U) S (atLetter (k i))) = _
      simp_rw [leg_k h he, vector, map_sum, map_smul, leg_b h he, vectorField_letter, a, vector]
      rw [show (∑ j : U, L j i • ∑ u : E, R u j • atLetter (k (U := U) u)) = _ from
          mul_line Lᵀ Rᵀ i _,
        show (∑ j : E, (-H i j) • ∑ u : E, (-C j u) • atLetter (k (U := U) u)) = _ from
          mul_line (-H) (-C) i _,
        neg_mul_neg]
      exact
        plus_line _ _ _ _
          (by
            rw [add_comm]
            exact hc.transposeRight)
    unfold letterD
    change
      classicalD (ports E U) S 0 + vectorField parity _ (classicalD (ports E U) S (atLetter (b i))) =
        _
    rw [map_zero, zero_add, leg_b h he, map_sum]
    simp_rw [map_smul, vectorField_letter, k, vector]
    rw [show (∑ j : E, R j i • ∑ u : U, L u j • atLetter (b (E := E) u)) = _ from mul_line Rᵀ Lᵀ i _,
      hc.transposeLeft]
    simp [b, Matrix.one_apply]

include h he hc in
/-- On pairs, check the quadratic moment identities that imply the formal integration by parts. -/
lemma WardCheck (x y : Letters E U) :
    ward (propagator C L) (ports E U) S x y +
        cross (parity x) (parity y) * ward (propagator C L) (ports E U) S y x =
      0 := by
  classical
  have hy (i : E) (j : E) : (R * L) i j + (H * C) j i = (1 : Matrix E E ℂ) i j := by
    rw [add_comm, ← hc.inverse, Matrix.add_apply]
    congr 1
    calc
      _ = (Cᵀ * Hᵀ) i j := congr_fun (congr_fun (transpose_mul H C) i) j
      _ = _ := by rw [hc.symmC, hc.symmH]
  have h1 (i j : E) :
    (((univ.filter fun x : E => x = j ∧ x = i).card) : ℂ) = (1 : Matrix E E ℂ) i j := by
    by_cases hh : i = j
    · subst j
      rw [show (univ.filter fun x : E => x = i ∧ x = i) = { i } from
          by
          ext
          simp]
      simp
    rw [Matrix.one_apply_ne hh]
    simp [show ∀ x : E, x = j → x ≠ i from fun x hk h' => hh (h'.symm.trans hk)]
  have h2 (i j : U) :
    (∑ x : U, (if x = j ∧ x = i then (-1 : ℂ) else 0)) + ∑ x : E, R x j * L i x = 0 := by
    have hw := congr_fun (congr_fun hc.transposeLeft j) i
    simp only [Matrix.mul_apply, transpose_apply] at hw
    rw [hw]
    by_cases he : i = j
    · subst i
      simp
    rw [Matrix.one_apply_ne (Ne.symm he), add_zero]
    exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => he (h.2.symm.trans h.1)))
  rcases x with (i | i) | (i | i) <;> rcases y with (j | j) | (j | j)
  all_goals
    simp_rw [ward, correlation]
    simp only [letterD, plain h, dual h,
      show ∀ q : E ⊕ U, (ports E U).fee q = (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) q) from
          fun q => by cases q <;> rfl,
      Pi.smul_apply, smul_eq_mul, at_D, he, Fintype.sum_sum_type]
    simp [lapEntry, symbol, parity, Letters, Fintype.sum_sum_type, covariance, ports, Bonded.fee]
  · rw [h1, ← hy]
    simp only [Matrix.mul_apply]
    abel
  · exact h2 _ _
  · rw [h1, ← hy]
    simp only [Matrix.mul_apply]
    abel
  exact h2 _ _

include h he hc

lemma Wick_cycle {F : Raw (Letters E U) ℂ} {C' : Matrix E E ℂ} {L' : Matrix U E ℂ}
    (he' : Splitting H R C' L') (hp : F ∈ Mini (Letters E U)) (hs : Symm parity F)
    (hf : quantumD (ports E U) S F = 0) : View (propagator C L) F = View (propagator C' L') F := by
  refine Contraction.Wick_eq h (contraction h he hc) ?_ ?_ hs hp hf
  · exact fun _ hx hy => stokes h clear (propSym hc.symmC) (WardCheck h he hc) hy hx
  exact fun _ hx hy => stokes h clear (propSym he'.symmC) (WardCheck h he he') hy hx

end st
end YM.WilsonMS.Darboux
