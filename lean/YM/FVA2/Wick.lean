import YM.FVA2.Letter
import YM.MS.Swirl.Mace

/-!
# Acyclic Gaussian Wick integration on orbit slices

The covariance is stated with its exact physical off-diagonal ghost sign
(`K,c` versus `c,K` derivative order) and the factor convention of `Master`.
The inverse-Hessian identities are one-letter, proved before e.g. turning on
any marks. These are not bounds and don't involve equality of diagrams as
assumptions. -/

set_option autoImplicit false
noncomputable section

namespace YM.FVA2.Letter
open Finset Function Matrix MS MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open MS.Koszul MS.Bare MS.Book MS.Cylinder MS.Swirl OddMatrix
variable {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]
variable {hes : Matrix X X ℂ} {grad : Matrix X Y ℂ}
  (cov : Matrix X X ℂ) (l : Matrix Y X ℂ)

def sigma : Matrix (Letter X Y) (Letter X Y) ℂ
| a i, a j => cov i j
| k i, c j => l j i
| c j, k i => -l j i
| _, _ => 0

def grain : Grain (Letter X Y) := fun i j => sigma cov l i j/2

omit [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
lemma chilled (i j : Letter X Y) : Chill (grain cov l) i j = sigma cov l i j := by
  unfold Chill grain; ring

omit [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
lemma clear_grain : Clear p (grain cov l) := by
  rintro (_|_|_|_) (_|_|_|_) hp <;> first | rfl | simp [sigma,grain] at hp

omit [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
lemma symm_grain (H : covᵀ=cov) : Cog.Sym p (grain cov l) := by
  rintro (i|i|i|i) (j|j|j|j) <;> simp [p,grain,sigma]
  rw [show cov i j=cov j i from congr_fun (congr_fun H j) i]
  all_goals ring

local infixl:70 " ⋄ " => product p

variable {cov l}
omit [DecidableEq X] [DecidableEq Y] in
lemma q_action (hes : Matrix X X ℂ) (grad : Matrix X Y ℂ) (F : Raw (Letter X Y) ℂ)
    (hf : Symm p F) :
    (Q hes grad).Q F =
      (-(∑ i:X,∑ j:X, hes j i • (atLetter (a i) ⋄ D (k j) F))
        + ∑ i:X,∑ j:Y, grad i j • (atLetter (k i) ⋄ D (b j) F))
        + ∑ i:Y,∑ j:X, grad j i • (atLetter (c i) ⋄ D (a j) F) := by
  rw [show (Q hes grad).Q F=_ from as_derivation p _ _ F hf,sum_all]
  simp_rw [hook_apply,sum_all]; simp [q]

/-- Wick IBP for the **flat** based master differential. -/
theorem ward (hes : Matrix X X ℂ) (grad : Matrix X Y ℂ)
    (hs : covᵀ=cov) (hm : l*grad=1)
    (hc : cov*hes=1-grad*l) (hh : hesᵀ=hes)
    (F : Raw (Letter X Y) ℂ) (he : Symm p F) (hp : F ∈ Mini _) :
    View (grain cov l) ((Δ (X:=X) (Y:=Y)+(Q hes grad).Q) F)=0 := by
  let W := View (grain cov l)
  let d (x y : Letter X Y) := W (D y (D x F))
  have hw (x y : Letter X Y) : W (atLetter x ⋄ D y F)=
      ∑ j, sigma cov l x j * d y j := by
    unfold W; rw [ibpV x (clear_grain cov l) (symm_grain cov l hs) (he.drop y) (miD hp y)]
    simp_rw [chilled]; rfl
  have hKA (i j) : W (atLetter (k i) ⋄ D j F) =
      ∑ t:Y, l t i * d j (c t) := by rw [hw,sum_all]; simp [sigma]
  have hAA (i j) : W (atLetter (a i) ⋄ D j F) =
      ∑ t:X, cov i t * d j (a t) := by rw [hw,sum_all]; simp [sigma]
  have hCK (i j) : W (atLetter (c i) ⋄ D j F) =
      -∑ t:X, l i t * d j (k t) := by rw [hw,sum_all]; simp [sigma]
  have hAK (x x' : X) : d (a x) (k x')=d (k x') (a x) := by
    unfold d; rw [he.commute (k x') (a x)]; simp [p]
  have K (j : Y) : (∑ i:X, grad i j * ∑ t:Y, l t i * d (b j) (c t))=d (b j) (c j) := by
    simp_rw [Finset.mul_sum, ← mul_assoc]; rw [Finset.sum_comm]
    simp_rw [mul_comm (grad _ j), ← Finset.sum_mul, ← Matrix.mul_apply, hm, Matrix.one_apply]
    simp [ite_mul]
  have A (j : X) :
      (∑ i:X, hes j i * ∑ t:X, cov i t * d (k j) (a t)) =
      ∑ t:X, ((1:Matrix X X ℂ)-grad*l) t j * d (k j) (a t) := by
    simp_rw [Finset.mul_sum, ← mul_assoc]; rw [Finset.sum_comm,← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply,Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show hes j x=hes x j from congr_fun (congr_fun hh x) j,
        show cov x i=cov i x from congr_fun (congr_fun hs i) x,
        mul_comm (hes _ _) (cov _ _)]
  have B (j : X) :
      (∑ i:Y, grad j i * ∑ t:X, l i t * d (a j) (k t)) =
      ∑ t:X,(grad*l) j t * d (k t) (a j) := by
    simp_rw [Finset.mul_sum, hAK,← mul_assoc]
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, ← Matrix.mul_apply]
  have YK : (∑ j:X,∑ t:X, ((1:Matrix X X ℂ)-grad*l) t j*d (k j) (a t)) =
      (∑ j:X,d (k j) (a j)) - ∑ t:X,∑ j:X,(grad*l) t j * d (k j) (a t) := by
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    simp only [Matrix.one_apply,ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]; rw [sub_right_inj]
    exact Finset.sum_comm
  change W (Δ F + (Q hes grad).Q F) = 0
  rw [map_add,q_action hes grad F he,delta]
  simp_rw [map_add,map_sub,map_neg,map_sum,map_smul,smul_eq_mul,hKA,hAA,hCK,mul_neg, sum_neg_distrib]
  rw [Finset.sum_comm (f:=fun (i:X) (j:Y)=>grad i j *∑ t:Y, l t i*d (b j) (c t)),
    Finset.sum_comm (f:=fun (i:X) (j:X)=>hes j i *∑ t:X, cov i t * d (k j) (a t)),
    Finset.sum_comm (f:=fun (i:Y) (j:X)=>grad j i *∑ t:X, l i t*d (a j) (k t))]
  simp_rw [K,B,A,YK]
  unfold d; abel

/-- Inversion quotient gauges/intermediate realizations can have different
covariances, even for the A-slots. Closing tests in the **rooted** complex
eliminates this dependence. Neither denominator truncation nor bounds used. -/
theorem gauges_agree
    (hes : Matrix X X ℂ) (grad : Matrix X Y ℂ) (hv : hesᵀ=hes) (hz : hes*grad=0)
    (hs : covᵀ=cov) (hm : l*grad=1) (hc : cov*hes=1-grad*l)
    {U : Matrix X X ℂ} {r : Matrix Y X ℂ} (hU : Uᵀ=U) (hr : r*grad=1)
    (hu : U*hes=1-grad*r) (F : Raw (Letter X Y) ℂ)
    (hp : F ∈ Mini _) (hF : Symm p F)
    (hf : (Δ (X:=X) (Y:=Y)+(Q hes grad).Q) F=0) :
    View (grain cov l) F=View (grain U r) F := by
  obtain ⟨n,h⟩ := hp
  obtain ⟨c,V,hl,ht,H⟩ := RankDescent.constant_mod_exact (q_odd hes grad) (lower_odd cov l)
    h (q_contraction hv hs hm hc) limit_delta symm_delta (fun f hf => square f hv hz hf) hF hf
  rw [H,map_add,map_add,minView, minView, ward _ _ hs hm hc hv V ht (minH hl),
    ward _ _ hU hr hu hv V ht (minH hl)]

end YM.FVA2.Letter
