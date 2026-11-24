import YM.Marker.Truncated
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Finite exponent and polynomial log

Pure algebra. The argument with the Euler variable gives exact factorials on the *combined*
truncation algebra -- no coupling or source disk in this lemma.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02

open Polynomial
open scoped BigOperators

-- Ordinary power series conventions over a commutative ℂ-algebra. These definitions also
-- make sense on arbitrary inputs. The hypotheses in the theorems make them exp/log.
section
variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Finite exponential through degree `n`. -/
def expTerms (n : ℕ) (x : A) : A :=
  ∑ i ∈ Finset.range (n + 1), (i.factorial : ℂ)⁻¹ • x ^ i

/-- For `x = 1 + w`: sums terms of log(1+w) through degree `n`. -/
def logTerms (n : ℕ) (x : A) : A :=
  ∑ i ∈ Finset.range n, ((-1 : ℂ)^i / (↑(i + 1 : ℕ) : ℂ)) • (x - 1)^(i + 1)

private theorem derivative_term_exp (x : A) (i : ℕ) :
    let q : Polynomial A := C x * X
    derivative (((i + 1).factorial : ℂ)⁻¹ • q^(i+1)) =
      C x * (((i.factorial : ℂ)⁻¹) • q^i) := by
  intro q
  rw [derivative_smul, derivative_pow_succ]
  dsimp [q]
  rw [derivative_C_mul_X]
  simp_rw [Algebra.smul_def]
  have ht : (algebraMap ℂ (Polynomial A)) (↑((i+1).factorial) : ℂ)⁻¹ * C ((i:A) + 1) =
      (algebraMap ℂ (Polynomial A)) (↑i.factorial : ℂ)⁻¹ := by
    have hi : C ((i:A) + 1) = (algebraMap ℂ (Polynomial A)) (↑(i+1) : ℂ) := by simp
    rw [hi, ← map_mul, Nat.factorial_succ, Nat.cast_mul]
    congr 1
    push_cast
    field_simp
  rw [← ht]
  ring

private theorem derivative_term_log (p : Polynomial A) (i : ℕ) :
    derivative (((-1 : ℂ)^i / ↑(i+1 : ℕ)) • p^(i+1)) =
      (-p)^i * derivative p := by
  rw [derivative_smul, derivative_pow_succ]
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc]
  have ht : (algebraMap ℂ (Polynomial A)) ((-1 : ℂ)^i / ↑(i+1 : ℕ)) * C ((i:A) + 1) =
      (-1 : Polynomial A)^i := by
    have hi : C ((i:A) + 1) = (algebraMap ℂ (Polynomial A)) (↑(i+1) : ℂ) := by simp
    rw [hi, ← map_mul, div_mul_cancel₀]
    · simp
    · exact_mod_cast Nat.succ_ne_zero i
  rw [ht, ← mul_pow]
  simp

private theorem derivative_expTerms (x : A) (n : ℕ) (hx : x^(n+1)=0) :
    derivative (expTerms n (C x * X)) = C x * expTerms n (C x * X) := by
  let q : Polynomial A := C x * X
  have he : C x * q^n = 0 := by
    rw [show C x * q^n = C (x^(n+1)) * X^n by
      dsimp [q]
      rw [map_pow]
      ring, hx, map_zero, zero_mul]
  unfold expTerms
  rw [map_sum]
  conv_lhs => rw [Finset.sum_range_succ']
  simp_rw [derivative_term_exp]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    derivative_one, add_zero]
  rw [Finset.mul_sum, Finset.sum_range_succ _ n, mul_smul_comm, he, smul_zero, add_zero]

private theorem derivative_logTerms (n : ℕ) (p : Polynomial A) :
    derivative (logTerms n p) = (∑ i ∈ Finset.range n, (1-p)^i) * derivative p := by
  unfold logTerms
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_term_log, derivative_sub]
  simp

private theorem nil_rebate (x : A) (n : ℕ) (hx : x^(n+1) = 0) :
    (1-expTerms n (C x * X))^n * C x = 0 := by
  let t : Polynomial A := C x * X
  have hh : C x ∣ expTerms n t - 1 := by
    unfold expTerms
    rw [Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, add_sub_cancel_right]
    refine Finset.dvd_sum fun i _ => ?_
    rw [pow_succ, show t=C x*X from rfl, Algebra.smul_def]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _
  have hy : C x ∣ 1-expTerms n t := by rw [← neg_sub (expTerms ..) 1]; exact dvd_neg.mpr hh
  obtain ⟨z, hz⟩ := hy
  change (1 - expTerms n t)^n * C x = _
  calc
    _ = C (x^(n+1)) * z^n := by rw [hz, map_pow]; ring
    _ = _ := by rw [hx, map_zero, zero_mul]

theorem logTerms_expTerms (x : A) {n : ℕ} (hx : x^(n+1)=0) :
    logTerms n (expTerms n x) = x := by
  let t : Polynomial A := C x * X
  let p := expTerms n t
  let L := logTerms n p
  have hd : derivative L = C x := by
    rw [show L = logTerms n p from rfl, derivative_logTerms, show derivative p = _ from derivative_expTerms x n hx]
    let q := 1-p
    have hq : (∑ i ∈ Finset.range n, q^i) * p = 1-q^n := by
      have hh := geom_sum_mul q n
      have he : q-1= -p := by dsimp [q]; ring
      rw [he, mul_neg] at hh
      rw [← neg_sub (q^n) 1, ← hh, neg_neg]
    change _*(C x * p) = _
    calc
      _ = ((∑ i ∈ Finset.range n, q^i)*p) * C x := by rw [mul_comm (C x) p, mul_assoc]
      _ = _ := by rw [hq, sub_mul, one_mul, show q^n*C x=0 from nil_rebate x n hx, sub_zero]
  have hc : L.eval 0 = 0 := by
    have he : p.eval 0 = 1 := by
      dsimp [p, expTerms, t]
      rw [eval_finsetSum]
      rw [Finset.sum_eq_single_of_mem 0 (by simp)]
      · simp
      · intro i hi hi'
        rw [eval_smul]
        simp [hi']
    dsimp [L, logTerms]
    rw [eval_finsetSum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [eval_smul]
    simp [he]
  have hLt : L = t := by
    have h : derivative (L - t) = 0 := by rw [derivative_sub, hd, show derivative t = _ from derivative_C_mul_X x, sub_self]
    have : IsAddTorsionFree A := .of_isTorsionFree ℂ A
    have hh := eq_C_of_derivative_eq_zero h
    apply sub_eq_zero.mp
    rwa [coeff_zero_eq_eval_zero, eval_sub, show eval 0 t=0 by simp [t], hc, sub_zero, map_zero] at hh
  calc
   _ = L.eval 1 := by
       dsimp only [L, p, t, expTerms, logTerms]
       rw [eval_finsetSum]
       congr! 1
       simp [eval_smul, eval_finsetSum]
   _ = _ := by rw [hLt]; simp [t]

end

end YM.Comparison.RG02
