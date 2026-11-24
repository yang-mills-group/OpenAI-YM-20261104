import YM.Space.Index
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
Homogeneous harmonic numerators for the one-leg detector calculation.
The dimension in these identities is four.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11
namespace ConeProbe

open MvPolynomial Finset
open scoped BigOperators Classical

abbrev Vec := Axis → ℂ
abbrev Pol := MvPolynomial Axis ℂ

def quad : Pol := ∑ i : Axis, X i * X i

def lap (p : Pol) : Pol := ∑ i : Axis, pderiv i (pderiv i p)

def euler (p : Pol) : Pol := ∑ i : Axis, X i * pderiv i p

lemma partial_comm (i j : Axis) (p : Pol) : pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  ext k
  by_cases h : i = j
  · subst i
    rfl
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, h, Ne.symm h,
    ↓reduceIte, add_zero]
  rw [add_right_comm k]
  ring

lemma partial_sq (i : Axis) : pderiv i quad = 2 * X i := by
  unfold quad
  rw [map_sum, Finset.sum_eq_single_of_mem i (mem_univ _)]
  · rw [pderiv_mul, pderiv_X_self]
    ring
  · intro j _ h
    rw [pderiv_mul, pderiv_X_of_ne h]
    ring

lemma euler_sq : euler quad = 2 * quad := by
  simp_rw [euler, partial_sq]
  rw [quad, mul_sum]
  exact sum_congr rfl fun i _ => by ring

lemma lap_X (i : Axis) (p : Pol) : lap (X i * p) = X i * lap p + 2 * pderiv i p := by
  have h (j : Axis) : pderiv j (pderiv j (X i * p)) =
      X i * pderiv j (pderiv j p) + if i=j then 2 * pderiv i p else 0 := by
    by_cases he : i = j
    · subst i
      simp only [pderiv_mul, pderiv_X_self, one_mul, map_add, if_true]
      ring
    · rw [if_neg he]
      simp only [pderiv_mul, pderiv_X_of_ne he, zero_mul, zero_add, add_zero]
  simp only [lap, h, Finset.sum_add_distrib, ← mul_sum]
  simp

lemma lap_sq_mul (p : Pol) : lap (quad * p) = quad * lap p + 4 * euler p + 8 * p := by
  have h (j : Axis) : pderiv j (pderiv j (quad * p)) = quad * pderiv j (pderiv j p) +
      4 * (X j * pderiv j p) + 2*p := by
    have hh (t : Axis) : pderiv t (2 : Pol) = 0 := by
      rw [show (2 : Pol) = 1+1 by ring, map_add, pderiv_one, add_zero]
    simp only [pderiv_mul, map_add, partial_sq, hh, zero_mul, zero_add, pderiv_X_self,
      mul_one]
    ring
  simp only [lap, h, Finset.sum_add_distrib, euler, ← Finset.mul_sum, Finset.sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma lap_add (p r : Pol) : lap (p+r) = lap p + lap r := by
  simp [lap,map_add,sum_add_distrib]

lemma lap_sub (p r : Pol) : lap (p-r) = lap p - lap r := by
  simp [lap,map_sub,sum_sub_distrib]

lemma lap_partial (p : Pol) (i : Axis) : lap (pderiv i p) = pderiv i (lap p) := by
  unfold lap
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [partial_comm j i p, partial_comm j i]

lemma lap_C_mul (z : ℂ) (p : Pol) : lap (C z * p) = C z * lap p := by
  simp only [lap, pderiv_C_mul, mul_sum]

lemma lap_C (z : ℂ) : lap (C z) = 0 := by simp only [lap,pderiv_C,map_zero,sum_const_zero]

lemma euler_mul (p r : Pol) : euler (p*r) = euler p*r + p*euler r := by
  unfold euler
  simp only [sum_mul, mul_sum, ← sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_mul]
  ring

lemma euler_X (i : Axis) : euler (X i) = X i := by
  unfold euler
  rw [Finset.sum_eq_single_of_mem i (mem_univ _), pderiv_X_self, mul_one]
  intro b _ hi
  rw [pderiv_X_of_ne (Ne.symm hi), mul_zero]

lemma euler_C (z : ℂ) : euler (C z) = 0 := by simp only [euler,pderiv_C,mul_zero,sum_const_zero]
lemma euler_add (p r : Pol) : euler (p+r) = euler p + euler r := by
  simp only [euler,map_add,mul_add,sum_add_distrib]
lemma euler_sub (p r : Pol) : euler (p-r) = euler p - euler r := by
  simp only [euler,map_sub,mul_sub,sum_sub_distrib]

lemma euler_partial (p : Pol) (j : Axis) : pderiv j (euler p) = euler (pderiv j p) + pderiv j p := by
  unfold euler
  rw [map_sum]
  have h (i : Axis) : pderiv j (X i * pderiv i p) =
      X i * pderiv i (pderiv j p) + if j=i then pderiv j p else 0 := by
    rw [pderiv_mul]
    by_cases he : i = j
    · subst i
      rw [pderiv_X_self, one_mul, if_pos rfl, add_comm]
    · rw [pderiv_X_of_ne he, zero_mul, zero_add, if_neg (Ne.symm he), add_zero, partial_comm]
  simp only [h, Finset.sum_add_distrib]
  simp

/-- Numerator recurrence for derivative of P / q^(n+1) in displacement coordinate i. -/
def raiseAt (i : Axis) (n : ℕ) (p : Pol) : Pol := quad * pderiv i p -
    C (2*((n:ℂ)+1)) * (X i * p)

structure HH (n : ℕ) (p : Pol) : Prop where
  hom : euler p = (n:Pol) * p
  harm : lap p = 0

namespace HH
variable {p q : Pol} {n : ℕ}
lemma zero (n : ℕ) : HH n 0 := ⟨by simp [euler], by simp [lap]⟩
lemma plus (h : HH n p) (k : HH n q) : HH n (p+q) :=
  ⟨by rw [euler_add, h.hom, k.hom, mul_add], by rw [lap_add,h.harm,k.harm,add_zero]⟩
lemma minus (h : HH n p) (k : HH n q) : HH n (p-q) :=
  ⟨by rw [euler_sub, h.hom, k.hom, mul_sub], by rw [lap_sub,h.harm,k.harm,sub_zero]⟩
lemma const_mul (h : HH n p) (z : ℂ) : HH n (C z * p) :=
  ⟨by rw [euler_mul, euler_C, zero_mul, zero_add, h.hom]; ring, by rw [lap_C_mul,h.harm,mul_zero]⟩
lemma constHH (z : ℂ) : HH 0 (C z) :=
  ⟨by simp only [euler_C, Nat.cast_zero, zero_mul], lap_C z⟩

lemma partial_euler (h : HH n p) (i : Axis) : euler (pderiv i p) = ((n:Pol)-1)*pderiv i p := by
  have he := euler_partial p i
  rw [h.hom, show (n:Pol) = C (n:ℂ) by simp, pderiv_C_mul, map_natCast] at he
  rw [sub_mul, one_mul, eq_sub_iff_add_eq, he]

lemma raise (h : HH n p) (i : Axis) : HH (n+1) (raiseAt i n p) where
  hom := by
    rw [raiseAt, euler_sub, euler_mul, euler_mul, euler_mul, h.hom, euler_C, euler_X, euler_sq,
      partial_euler h]
    push_cast
    ring
  harm := by
    rw [raiseAt, lap_sub, lap_sq_mul, lap_C_mul, lap_X, lap_partial, h.harm, map_zero,
      partial_euler h]
    simp only [map_mul, map_add, map_one, map_ofNat, map_natCast]
    ring
end HH
end ConeProbe
end YM.SchemeRG11
