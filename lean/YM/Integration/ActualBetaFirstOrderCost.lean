import YM.Integration.ActualBetaRetuningCost

noncomputable section

namespace YM.Integration.ActualBetaRemainder

open Finset

/-- The exact finite-copy expansion has constant coefficient one. -/
@[simp] theorem coefficient_zero (e : ℤ) : coefficient e 0 = 1 := by
  unfold coefficient
  exact Ring.choose_zero_right _

private theorem finite_coefficient_linear (e : ℤ) (A : ℝ)
    (hA : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, |coefficient e k| * (1 / 2 : ℝ) ^ k) ≤ A)
    (t : ℝ) (ht : |t| ≤ 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, |coefficient e k| * |t| ^ k) ≤
      1 + (2 * A) * |t| := by
  cases n with
  | zero => omega
  | succ n =>
    have hb := hA (n + 1)
    rw [Finset.sum_range_succ'] at hb
    rw [Finset.sum_range_succ']
    simp only [coefficient_zero, abs_one, pow_zero, mul_one] at hb ⊢
    have htail :
        (∑ k ∈ Finset.range n, |coefficient e (k + 1)| * |t| ^ (k + 1)) ≤
          (2 * |t|) *
            (∑ k ∈ Finset.range n,
              |coefficient e (k + 1)| * (1 / 2 : ℝ) ^ (k + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      calc
        |coefficient e (k + 1)| * |t| ^ (k + 1) =
            |t| * (|coefficient e (k + 1)| * |t| ^ k) := by
          rw [pow_succ]
          ring
        _ ≤ |t| * (|coefficient e (k + 1)| * (1 / 2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (abs_nonneg t) ht k) (abs_nonneg _))
            (abs_nonneg t)
        _ = (2 * |t|) *
            (|coefficient e (k + 1)| * (1 / 2 : ℝ) ^ (k + 1)) := by
          rw [pow_succ]
          ring
    have htailA :
        (∑ k ∈ Finset.range n,
          |coefficient e (k + 1)| * (1 / 2 : ℝ) ^ (k + 1)) ≤ A := by
      linarith
    calc
      _ ≤ (2 * |t|) *
          (∑ k ∈ Finset.range n,
            |coefficient e (k + 1)| * (1 / 2 : ℝ) ^ (k + 1)) + 1 :=
        add_le_add htail (le_refl 1)
      _ ≤ (2 * |t|) * A + 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left htailA (by positivity)) (le_refl 1)
      _ = 1 + (2 * A) * |t| := by ring

/-- Absolute coefficient summability at one half yields a first-order bill,
uniform over the finite exponent cap and every positive truncation order. -/
theorem coefficientBill_first_order (cap : ℕ) :
    ∃ D > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      |delta * g ^ 2| ≤ 1 / 2 → ∀ n : ℕ, 1 ≤ n →
        coefficientBill e delta g n ≤ 1 + D * |delta * g ^ 2| := by
  obtain ⟨A, hA, hbound⟩ := capped_coefficient_budget cap
  refine ⟨2 * A, by positivity, ?_⟩
  intro e he delta g ht n hn
  rw [coefficientBill_eq]
  apply finite_coefficient_linear e A _ (delta * g ^ 2) ht n hn
  intro m
  simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
    hbound e he (1 / 2) (by norm_num) m

/-- The exact correction at the same nonzero physical coupling has a
first-order bill; its original division by the physical power is retained. -/
theorem correction_physical_first_order (cap : ℕ) :
    ∃ D > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      g ≠ 0 → |delta * g ^ 2| ≤ 1 / 2 → ∀ n : ℕ, 1 ≤ n →
        |correctionCoefficient e delta g n| * |g| ^ (2 * n) ≤
          D * |delta * g ^ 2| := by
  obtain ⟨C, hC, hbound⟩ := unit_power_remainder cap
  refine ⟨C * (4 / 3 : ℝ), by positivity, ?_⟩
  intro e he delta g hg ht n hn
  have hid :
      |correctionCoefficient e delta g n| * |g| ^ (2 * n) =
        |unit delta g ^ e - truncated e n (delta * g ^ 2)| := by
    rw [correctionCoefficient, abs_div, abs_pow]
    exact div_mul_cancel₀ _ (pow_pos (abs_pos.mpr hg) (2 * n)).ne'
  have hbase0 : 0 ≤ (4 / 3 : ℝ) * |delta * g ^ 2| := by positivity
  have hbase1 : (4 / 3 : ℝ) * |delta * g ^ 2| ≤ 1 := by
    nlinarith
  have hpow :
      ((4 / 3 : ℝ) * |delta * g ^ 2|) ^ n ≤
        (4 / 3 : ℝ) * |delta * g ^ 2| :=
    pow_le_of_le_one hbase0 hbase1 (by omega : n ≠ 0)
  calc
    _ = |unit delta g ^ e - truncated e n (delta * g ^ 2)| := hid
    _ ≤ C * (4 / 3 : ℝ) ^ n * |delta| ^ n * |g| ^ (2 * n) :=
      hbound e he delta g ht n
    _ = C * ((4 / 3 : ℝ) * |delta * g ^ 2|) ^ n := by
      simp only [abs_mul, abs_pow, mul_pow, ← pow_mul]
      ring
    _ ≤ C * ((4 / 3 : ℝ) * |delta * g ^ 2|) :=
      mul_le_mul_of_nonneg_left hpow hC.le
    _ = (C * (4 / 3 : ℝ)) * |delta * g ^ 2| := by ring

/-- The full exact finite-copy retuning cost is one plus a first-order error.
No product over steps or trajectory summability is asserted. -/
theorem full_retuning_first_order (cap : ℕ) :
    ∃ D > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      g ≠ 0 → |delta * g ^ 2| ≤ 1 / 2 → ∀ n : ℕ, 1 ≤ n →
        coefficientBill e delta g n +
          |correctionCoefficient e delta g n| * |g| ^ (2 * n) ≤
            1 + D * |delta * g ^ 2| := by
  obtain ⟨A, hA, hcoefficient⟩ := coefficientBill_first_order cap
  obtain ⟨B, hB, hcorrection⟩ := correction_physical_first_order cap
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro e he delta g hg ht n hn
  calc
    _ ≤ (1 + A * |delta * g ^ 2|) + B * |delta * g ^ 2| :=
      add_le_add (hcoefficient e he delta g ht n hn)
        (hcorrection e he delta g hg ht n hn)
    _ = 1 + (A + B) * |delta * g ^ 2| := by ring

end YM.Integration.ActualBetaRemainder

end
