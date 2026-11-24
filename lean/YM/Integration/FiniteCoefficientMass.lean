import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

/-! Finite triangular coefficient growth.  The degree depends only on the
number of coefficients and the fixed power.  No parameter of the coefficient
sequence is used to select the resulting polynomial degree or constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FiniteCoefficientMass
open scoped BigOperators

def mass (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range n, |c j|

def degree (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => degree q n * q + 1

private lemma mass_one_le (c : ℕ → ℝ) (n : ℕ) : 1 ≤ mass c n := by
  have h : 0 ≤ ∑ j ∈ Finset.range n, |c j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (c j))
  unfold mass
  linarith

private lemma mass_succ (c : ℕ → ℝ) (n : ℕ) :
    mass c (n + 1) = mass c n + |c n| := by
  unfold mass
  rw [Finset.sum_range_succ]
  ring

/-- A finite triangular recurrence gives a fixed power of its one coefficient. -/
theorem mass_bound (c : ℕ → ℝ) (q n : ℕ) (K : ℝ)
    (hq : 1 ≤ q) (hK : 0 ≤ K)
    (hc : ∀ j < n, |c j| ≤ K * mass c j ^ q) :
    mass c n ≤ (1 + K) ^ degree q n := by
  revert hc
  induction n with
  | zero => intro _; simp [mass, degree]
  | succ n ih =>
      intro hc
      have hi := ih (fun j hj => hc j (Nat.lt_succ_of_lt hj))
      have hm := mass_one_le c n
      have hp : mass c n ≤ mass c n ^ q := by
        simpa only [pow_one] using pow_le_pow_right₀ hm hq
      calc
        mass c (n + 1) = mass c n + |c n| := mass_succ c n
        _ ≤ mass c n ^ q + K * mass c n ^ q :=
          add_le_add hp (hc n (Nat.lt_succ_self n))
        _ = (1 + K) * mass c n ^ q := by ring
        _ ≤ (1 + K) * ((1 + K) ^ degree q n) ^ q :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (zero_le_one.trans hm) hi q) (by linarith)
        _ = (1 + K) ^ degree q (n + 1) := by
          simp only [degree, pow_add, pow_mul, pow_one]
          ring

/-- Substituting a polynomial coefficient keeps the resulting degree fixed
before the sequence and the value of its scalar parameter. -/
theorem polynomial_bound (q n d : ℕ) (C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (t : ℝ) (ht : 1 ≤ t) (c : ℕ → ℝ)
    (hc : ∀ j < n, |c j| ≤ (C * t ^ d) * mass c j ^ q) :
    mass c n ≤ (1 + C) ^ degree q n * t ^ (d * degree q n) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hp : 1 ≤ t ^ d := by
    simpa only [pow_zero] using pow_le_pow_right₀ ht (Nat.zero_le d)
  have hK : 0 ≤ C * t ^ d := mul_nonneg hC (pow_nonneg ht0 d)
  have hb : 1 + C * t ^ d ≤ (1 + C) * t ^ d := by nlinarith
  calc
    mass c n ≤ (1 + C * t ^ d) ^ degree q n :=
      mass_bound c q n (C * t ^ d) hq hK hc
    _ ≤ ((1 + C) * t ^ d) ^ degree q n :=
      pow_le_pow_left₀ (by linarith) hb _
    _ = (1 + C) ^ degree q n * t ^ (d * degree q n) := by
      rw [mul_pow, ← pow_mul]

end YM.Integration.FiniteCoefficientMass
end
