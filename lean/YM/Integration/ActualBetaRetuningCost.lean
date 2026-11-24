import YM.Integration.ActualBetaRemainder

/-!
The entire finite-copy coefficient bill for the same beta reset.
Absolute coefficient sums are bounded using the radius of the actual
binomial series. The bound is uniform in the truncation order.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualBetaRemainder

open Finset
open scoped NNReal ENNReal

theorem coefficient_summable (e : ℤ) :
    Summable (fun k : ℕ => |coefficient e k| * (1 / 2 : ℝ) ^ k) := by
  have hr : ((1 / 2 : ℝ≥0) : ℝ≥0∞) < (series e).radius :=
    lt_of_lt_of_le (by norm_num) (factor_series e).r_le
  simpa [series, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using
    (series e).summable_norm_mul_pow (r := (1 / 2 : ℝ≥0)) hr

theorem exponent_coefficient_budget (e : ℤ) :
    ∃ C > 0, ∀ t : ℝ, |t| ≤ 1 / 2 → ∀ n : ℕ,
      (∑ k ∈ Finset.range n, |coefficient e k| * |t| ^ k) ≤ C := by
  let S : ℝ := ∑' k : ℕ, |coefficient e k| * (1 / 2 : ℝ) ^ k
  have hS : 0 ≤ S := tsum_nonneg (fun k => by positivity)
  refine ⟨1 + S, by linarith, ?_⟩
  intro t ht n
  calc
    (∑ k ∈ Finset.range n, |coefficient e k| * |t| ^ k)
        ≤ ∑ k ∈ Finset.range n, |coefficient e k| * (1 / 2 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro k _hk
          gcongr
    _ ≤ S := (coefficient_summable e).sum_le_tsum _ (fun k _ => by positivity)
    _ ≤ 1 + S := by linarith

theorem capped_coefficient_budget (cap : ℕ) :
    ∃ C > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ t : ℝ, |t| ≤ 1 / 2 → ∀ n : ℕ,
      (∑ k ∈ Finset.range n, |coefficient e k| * |t| ^ k) ≤ C := by
  classical
  choose B hB hbound using exponent_coefficient_budget
  let powers := Finset.Icc (-(cap : ℤ)) (cap : ℤ)
  have hsum : 0 ≤ ∑ e ∈ powers, B e :=
    Finset.sum_nonneg (fun e _ => (hB e).le)
  refine ⟨1 + ∑ e ∈ powers, B e, by linarith, ?_⟩
  intro e he t ht n
  have hmem : e ∈ powers := Finset.mem_Icc.mpr (abs_le.mp he)
  have hle : B e ≤ 1 + ∑ j ∈ powers, B j := by
    have := Finset.single_le_sum (fun j _ => (hB j).le) hmem
    linarith
  exact (hbound e t ht n).trans hle

def coefficientBill (e : ℤ) (delta g : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, |coefficient e k| * |delta| ^ k * |g| ^ (2 * k)

theorem coefficientBill_eq (e : ℤ) (delta g : ℝ) (n : ℕ) :
    coefficientBill e delta g n =
      ∑ k ∈ Finset.range n, |coefficient e k| * |delta * g ^ 2| ^ k := by
  unfold coefficientBill
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [abs_mul, abs_pow, mul_pow, ← pow_mul]
  ring

theorem actual_coefficient_budget (cap : ℕ) :
    ∃ C > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      |delta * g ^ 2| ≤ 1 / 2 → ∀ n : ℕ,
      coefficientBill e delta g n ≤ C := by
  obtain ⟨C, hC, hbound⟩ := capped_coefficient_budget cap
  refine ⟨C, hC, ?_⟩
  intro e he delta g hsmall n
  rw [coefficientBill_eq]
  exact hbound e he (delta * g ^ 2) hsmall n

/-- The new correction copy has a geometrically decreasing physical bill,
even though its bare coefficient contains the necessary delta powers. -/
theorem correction_physical_decay (cap : ℕ) :
    ∃ C > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      g ≠ 0 → |delta * g ^ 2| ≤ 1 / 2 → ∀ n : ℕ,
      |correctionCoefficient e delta g n| * |g| ^ (2 * n) ≤
        C * (2 / 3 : ℝ) ^ n := by
  obtain ⟨C, hC, hbound⟩ := unit_power_remainder cap
  refine ⟨C, hC, ?_⟩
  intro e he delta g hg hsmall n
  have hid : |correctionCoefficient e delta g n| * |g| ^ (2 * n) =
      |unit delta g ^ e - truncated e n (delta * g ^ 2)| := by
    rw [correctionCoefficient, abs_div, abs_pow]
    exact div_mul_cancel₀ _ (pow_pos (abs_pos.mpr hg) (2 * n)).ne'
  have hbase : (4 / 3 : ℝ) * |delta * g ^ 2| ≤ 2 / 3 := by
    nlinarith
  rw [hid]
  calc
    |unit delta g ^ e - truncated e n (delta * g ^ 2)|
        ≤ C * (4 / 3 : ℝ) ^ n * |delta| ^ n * |g| ^ (2 * n) :=
          hbound e he delta g hsmall n
    _ = C * ((4 / 3 : ℝ) * |delta * g ^ 2|) ^ n := by
      simp only [abs_mul, abs_pow, mul_pow, ← pow_mul]
      ring
    _ ≤ C * (2 / 3 : ℝ) ^ n := by
      gcongr

/-- The full triangle bill of every polynomial copy plus the correcting
copy has one cap-dependent bound before n, delta, and g are selected. -/
theorem full_retuning_cost (cap : ℕ) :
    ∃ C > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      g ≠ 0 → |delta * g ^ 2| ≤ 1 / 2 → ∀ n : ℕ,
      coefficientBill e delta g n +
        |correctionCoefficient e delta g n| * |g| ^ (2 * n) ≤ C := by
  obtain ⟨A, hA, hpoly⟩ := actual_coefficient_budget cap
  obtain ⟨B, hB, hcorrection⟩ := correction_physical_decay cap
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro e he delta g hg hsmall n
  have hpow : (2 / 3 : ℝ) ^ n ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hdecay : B * (2 / 3 : ℝ) ^ n ≤ B := by
    simpa using mul_le_mul_of_nonneg_left hpow hB.le
  exact add_le_add (hpoly e he delta g hsmall n)
    ((hcorrection e he delta g hg hsmall n).trans hdecay)

end YM.Integration.ActualBetaRemainder
end
