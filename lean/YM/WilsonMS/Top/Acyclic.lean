import YM.WilsonMS.Top.Polynomial
import YM.MS.Book.Chants

/-!
# Changing linear gauge on LPT coefficients (algebra)

Work in the Koszul/Swirl algebra of the MS theorem. Finite-dimensional,
*after* scaling the fields so the Gaussian has no coupling dependence. BV
lemma: if the free, linear BV complex contracts on the field letters, **two
Wick computations** which integrate the free BV differential to zero on
polynomials agree on its cycles. No positivity needed and no determinant
formula assumed for the Grassmann part. Will use with `Symm` polynomials
coefficient by coefficient including on the insertion products.

It's essential here that *all* zero modes be accounted for before trying this
argument. In particular we mustn't ask for a contraction as below on a complex
with the constant ghost included!
-/

set_option autoImplicit false
noncomputable section

namespace YM.WilsonMS

open MS MS.Koszul MS.Cylinder MS.Book MS.Swirl MS.Orbit MS.Orbit.Cog Finset

variable {A I : Type} [Fintype A] [Fintype I] {p : Sector A} (B : Bonded p I) (S : Raw A ℂ)
  {s : A → Raw A ℂ} {F : Raw A ℂ}

/-- A free BV exponent on this alphabet, in ℂ convention (wilson part
includes minus sign). -/
structure Quadratic : Prop where
  rank : Book.rank 2 S
  even : Pure p false S
  symm : Symm p S
  lap : B.BV S = 0
  master : link B.BV true p S S = 0

def classicalD : Op A ℂ :=
  tokenL B.BV true p S

def quantumD : Op A ℂ :=
  classicalD B S + B.BV

omit [Fintype A] in
lemma classical_apply (F : Raw A ℂ) : classicalD B S F = link B.BV true p S F :=
  rfl

omit [Fintype A] in
lemma quantum_apply (F : Raw A ℂ) : quantumD B S F = classicalD B S F + B.BV F :=
  rfl

def letterD (i : A) :=
  classicalD B S (atLetter i)

variable {B S} (h : Quadratic B S)
include h

namespace Quadratic

omit [Fintype A] in
lemma promotesField : OddField p (letterD B S)
    where
  rank
    i := by
    change Book.rank _ (link B.BV true p S _)
    rw [Bonded.by_lap B h.even]
    apply Rails.sum
    intro j _
    have ha (a : A) : Book.rank 1 (D a S) := h.rank.enter a
    have hx : Book.rank 1 (atLetter i (R := ℂ)) := Rails.letter i
    have hb (a : A) : Book.rank 0 (D a (atLetter i (R := ℂ))) := hx.enter a
    exact Rails.smul _ (Rails.add ((ha _).product (hb _)) ((ha _).product (hb _)))
  odd
    i := by
    have hv := speaks_p (p := p) (R := ℂ) i
    change Pure p _ (link B.BV true p S (atLetter i))
    have he := link_pure (b := true) B.BV (fun _ _ he => B.costs.pure he) h.even hv
    simpa only [Bool.false_xor, Bool.xor_true] using he

omit h in
private lemma collect (a : Raw A ℂ) (F : Raw A ℂ) (i : A) :
    (∑ j : A, product p (product p a (D i (atLetter j))) (D j F)) = product p a (D i F) := by
  classical
  rw [Finset.sum_eq_single_of_mem i (mem_univ i), hear, ← (coin_pure 1).central, coin_product,
    one_smul]
  intro j _ hj
  rw [unheard _ (Ne.symm hj), map_zero, map_zero]
  rfl

lemma classical_vector : classicalD B S = vectorField p (letterD B S) := by
  ext1 U
  rw [classical_apply, vectorField_eq]
  simp_rw [letterD, classical_apply, B.by_lap h.even]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_add,
    LinearMap.add_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.smul_sum, Finset.sum_add_distrib, collect, collect]

lemma classical_rank {r : ℤ} (hF : Book.rank r F) : Book.rank r (classicalD B S F) := by
  rw [h.classical_vector]
  exact h.promotesField.keepsRank hF

omit [Fintype A] in
lemma classical_limit {r : ℤ} (hF : Limit F r) : Limit (classicalD B S F) r := by
  rw [classical_apply]
  rw [show r = 2 + r - 2 by omega]
  exact roofLink B (rank_limit h.rank) hF

lemma classical_symmetric (hF : Symm p F) : Symm p (classicalD B S F) := by
  rw [h.classical_vector]
  exact h.promotesField.symmetric hF

omit [Fintype A] in
lemma classical_square (hF : Symm p F) : classicalD B S (classicalD B S F) = 0 := by
  have he := B.costs.double_j h.even h.symm hF
  change
    (2 : ℕ) • classicalD B S (classicalD B S F) + link B.BV true p (link B.BV true p S S) F = 0 at he
  rw [h.master,
    show link B.BV true p 0 F = 0 from LinearMap.congr_fun (map_zero (tokenL B.BV true p)) F,
    add_zero] at he
  exact two_nsmul_eq_zero.mp he

lemma quantum_symmetric (hF : Symm p F) : Symm p (quantumD B S F) :=
  (h.classical_symmetric hF).add (loop_symm hF)

omit [Fintype A] in
lemma quantum_square (hF : Symm p F) : quantumD B S (quantumD B S F) = 0 := by
  have he := B.costs.anti_j h.even h.symm hF
  change B.BV (classicalD B S F) + classicalD B S (B.BV F) + link B.BV true p (B.BV S) F = 0 at he
  rw [h.lap, show link B.BV true p 0 F = 0 from LinearMap.congr_fun (map_zero (tokenL B.BV true p)) F,
    add_zero] at he
  rw [quantum_apply, quantum_apply, map_add, map_add, h.classical_square hF,
    (show B.BV (B.BV F) = 0 from B.costs.quits hF)]
  linear_combination (norm := abel) he

end Quadratic

omit h

/-- Test for acyclicity on the field/antifield letters (classical rank-1 complex). -/
structure Contraction (s : A → Raw A ℂ) (B : Bonded p I) (S : Raw A ℂ) : Prop where
  form : OddField p s
  contracts i : classicalD B S (s i) + vectorField p s (letterD B S i) = atLetter i

variable (H : Contraction s B S)

namespace Contraction

include H h

lemma lift_rank (n : ℕ) (hr : Book.rank (n + 1 : ℕ) F) (hs : Symm p F) (hf : classicalD B S F = 0) :
    ∃ v : Raw A ℂ, Book.rank (n + 1 : ℕ) v ∧ Symm p v ∧ classicalD B S v = F := by
  let r : ℂ := (n + 1 : ℕ)
  have hp : r ≠ 0 := by
    unfold r
    exact_mod_cast (Nat.succ_ne_zero n)
  have hx :=
    anticommutator h.promotesField H.form
      (fun i => by
        rw [← h.classical_vector]
        exact H.contracts i)
      hr hs
  let V := vectorField p s F
  refine ⟨r⁻¹ • V, Rails.smul _ (H.form.keepsRank hr), Symm.smul _ (H.form.symmetric hs), ?_⟩
  rw [← h.classical_vector, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hf,
    map_zero, add_zero] at hx
  rw [map_smul, show classicalD B S V = r • F from hx, inv_smul_smul₀ hp]

/-- The free-interaction part of the differential preserves field rank. The
BV-Laplacian *lowers* rank. Lift in the former differential first at the top
arity (up to constants if no letters left). Subtract the *full* differential
of that lift and induct on arity. -/
lemma polynomial (n : ℕ) (hv : Limit F n) (hs : Symm p F) (hq : quantumD B S F = 0) :
    ∃ (x : ℂ) (v : Raw A ℂ), Limit v n ∧ Symm p v ∧ F = coin x + quantumD B S v := by
  induction n generalizing F with
  | zero =>
    exact
      ⟨F [], 0, fun l _ => rfl, Symm.zero,
        by
        rw [map_zero, add_zero]
        exact limit_zero_coin (by exact_mod_cast hv)⟩
  | succ n ih =>
    let k : ℤ := (n + 1 : ℕ)
    let U := mask k F
    have hU : Book.rank k U := rankMod F k
    have hN : Limit (F - U) n := limit_sub_mask hv
    have ht (Z : Raw A ℂ) (HZ : Limit Z (↑n)) : mask k Z = 0 := by
      ext l
      by_cases hx : (l.length : ℤ) = k
      · exact
          (enough l hx).trans
            (HZ l
              (by
                dsimp only [k] at hx
                omega))
      exact strange l hx
    have hF : mask k (classicalD B S F) = 0 := by
      rw [quantum_apply] at hq
      replace hq := congr_arg (mask k) hq
      simp only [map_add, map_zero] at hq
      rw [ht _ (Limit.up (roofLap B hv) (by omega)), add_zero] at hq
      exact hq
    have hH : classicalD B S U = 0 := by
      have hh := ht _ (h.classical_limit hN)
      rw [map_sub, map_sub, hF, zero_sub, (rank_hat _).mp (h.classical_rank hU)] at hh
      exact neg_eq_zero.mp hh
    obtain ⟨v, hL, hv', he⟩ := lift_rank h H n hU (mask_symmetric k hs) hH
    let W := F - quantumD B S v
    have hw : Limit W n := by
      unfold W
      rw [quantum_apply, he, sub_add_eq_sub_sub]
      exact Limit.sub hN (Limit.up (roofLap B (rank_limit hL)) (by omega))
    obtain ⟨x, u, hV, hh, hx⟩ :=
      ih hw (hs.sub (h.quantum_symmetric hv'))
        (by
          unfold W
          rw [map_sub, hq, h.quantum_square hv', sub_zero])
    refine ⟨x, u + v, (Limit.up hV (by omega)).add (rank_limit hL), hh.add hv', ?_⟩
    rw [map_add, ← add_assoc, ← hx]
    exact (sub_add_cancel ..).symm

/-- Finite-dimensional BV gauge-fixing principle adequate for our gauge change. -/
lemma Wick_eq {K L : Grain A} (hk : ∀ v ∈ Mini A, Symm p v → View K (quantumD B S v) = 0)
    (hl : ∀ v ∈ Mini A, Symm p v → View L (quantumD B S v) = 0) (he : Symm p F) (hv : F ∈ Mini A)
    (hf : quantumD B S F = 0) : View K F = View L F := by
  obtain ⟨n, hv⟩ := hv
  obtain ⟨x, v, hN, hV, rfl⟩ := polynomial h H n hv he hf
  rw [map_add, map_add, hk v (minH hN) hV, hl v (minH hN) hV, minView, minView]

end Contraction
end YM.WilsonMS
