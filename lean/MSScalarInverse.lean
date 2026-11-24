import FormalConversion

/-! Reversion of the position detector in the coupling convention used to
convert the correlation and OPE coefficients. -/
set_option autoImplicit false
noncomputable section

namespace YangMills.MSbar.Series

open Matching (couplingPower)
open scoped BigOperators

/-- The constant and linear coefficients fix the origin and the tangent.
Each higher coefficient uses only the already computed coefficients. -/
def inverseCoupling (χ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n+2 =>
    -∑ j ∈ Finset.range (n+1), χ (j+2) *
      couplingPower (fun i => if _ : i < n+2 then inverseCoupling χ i else 0) (j+2) (n+2)
termination_by n => n

@[simp] theorem inverseCoupling_zero (χ : ℕ → ℝ) : inverseCoupling χ 0 = 0 := by
  rw [inverseCoupling]

@[simp] theorem inverseCoupling_one (χ : ℕ → ℝ) : inverseCoupling χ 1 = 1 := by
  rw [inverseCoupling]

private theorem power_one (f : ℕ → ℝ) (n : ℕ) : couplingPower f 1 n = f n := by
  classical
  change (∑ i : Fin (n+1), f i.val * (if n-i.val = 0 then 1 else 0)) = f n
  rw [Finset.sum_eq_single (⟨n, by omega⟩ : Fin (n+1))]
  · simp
  · intro i _ hi
    have : i.val ≠ n := fun h => hi (Fin.ext h)
    have hlt : i.val < n+1 := i.isLt
    simp [show n-i.val ≠ 0 by omega]
  · simp

private theorem positive_power_at_zero {f : ℕ → ℝ} (hf : f 0 = 0) (j : ℕ) :
    couplingPower f (j+1) 0 = 0 := by
  simp [couplingPower, hf]

private theorem power_congr {f g : ℕ → ℝ} (j n : ℕ) (h : ∀ i ≤ n, f i = g i) :
    couplingPower f j n = couplingPower g j n := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    apply Finset.sum_congr rfl
    intro i _
    rw [h i.val (Nat.le_of_lt_succ i.isLt), ih (n-i.val) (fun l hl =>
      h l (le_trans hl (Nat.sub_le n i.val)))]

/-- If at least two factors vanish at the origin, a coefficient of their
power is unchanged by dropping the input coefficients at and above that order. -/
private theorem cutoff_power {f : ℕ → ℝ} (hf : f 0 = 0) (j n : ℕ) :
    couplingPower (fun i => if i < n then f i else 0) (j+2) n =
      couplingPower f (j+2) n := by
  let cut (i : ℕ) := if i < n then f i else 0
  have h0 : cut 0 = 0 := by simp [cut, hf]
  change (∑ i : Fin (n+1), cut i.val * couplingPower cut (j+1) (n-i.val)) =
    ∑ i : Fin (n+1), f i.val * couplingPower f (j+1) (n-i.val)
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val = 0
  · simp only [hi, h0, hf, zero_mul]
  by_cases hn : i.val = n
  · simp only [hn, Nat.sub_self, positive_power_at_zero h0, positive_power_at_zero hf, mul_zero]
  have hle : i.val < n := lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hn
  rw [show cut i.val = f i.val by simp [cut, hle]]
  rw [power_congr (f := cut) (g := f) (j+1) (n-i.val) (fun l hl => by
    have : l < n := by omega
    simp [cut, this])]

/-- The independent detector composed with its triangular inverse equals
the identity series coefficient by coefficient. -/
theorem coupling_after_inverse (χ : ℕ → ℝ) (h₀ : χ 0 = 0) (h₁ : χ 1 = 1) (k : ℕ) :
    (∑ j ∈ Finset.range (k+1), χ j * couplingPower (inverseCoupling χ) j k) =
      if k = 1 then 1 else 0 := by
  classical
  match k with
  | 0 => simp [h₀]
  | 1 => simp [Finset.sum_range_succ, h₀, h₁, power_one]
  | n+2 =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [h₀, zero_mul, add_zero, h₁, one_mul, power_one, Nat.reduceAdd]
    rw [show inverseCoupling χ (n+2) = _ from inverseCoupling.eq_3 χ n]
    simp only [dite_eq_ite]
    simp_rw [cutoff_power (inverseCoupling_zero χ)]
    simp

@[simp] theorem inverseCoupling_two (χ : ℕ → ℝ) : inverseCoupling χ 2 = -χ 2 := by
  rw [inverseCoupling.eq_3 χ 0]
  simp only [Finset.sum_range_one, zero_add, dite_eq_ite]
  rw [cutoff_power (inverseCoupling_zero χ) 0 2]
  change -(χ 2 * ∑ i : Fin 3, inverseCoupling χ i.val *
    couplingPower (inverseCoupling χ) 1 (2-i.val)) = -χ 2
  simp [Fin.sum_univ_succ, power_one]

end YangMills.MSbar.Series

