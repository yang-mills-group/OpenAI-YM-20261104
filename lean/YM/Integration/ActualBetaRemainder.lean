import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Interval

/-!
A quantitative remainder for the actual signed beta-reset factor.
The constant is chosen from the finite exponent cap before the coupling,
beta difference, truncation order, or test data. The final correction retains
the exact value at a specified nonzero physical coupling.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualBetaRemainder

open Finset Asymptotics Filter
open scoped Topology NNReal

def coefficient (e : ℤ) (k : ℕ) : ℝ :=
  Ring.choose ((e : ℝ) / 2 + k - 1) k

def series (e : ℤ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (coefficient e)

def factor (e : ℤ) (t : ℝ) : ℝ :=
  1 / (1 - t) ^ ((e : ℝ) / 2)

/-- The polynomial has precisely the powers strictly below n. -/
def truncated (e : ℤ) (n : ℕ) (t : ℝ) : ℝ :=
  (series e).partialSum n t

def unit (delta g : ℝ) : ℝ :=
  (Real.sqrt (1 - delta * g ^ 2))⁻¹

theorem factor_series (e : ℤ) :
    HasFPowerSeriesOnBall (factor e) (series e) 0 1 := by
  exact Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero ((e : ℝ) / 2)

theorem truncated_sum (e : ℤ) (n : ℕ) (t : ℝ) :
    truncated e n t = ∑ k ∈ Finset.range n, coefficient e k * t ^ k := by
  simp [truncated, series, FormalMultilinearSeries.partialSum, mul_comm]

theorem factor_eq_unit_power (e : ℤ) (t : ℝ) (ht : 0 ≤ 1 - t) :
    factor e t = ((Real.sqrt (1 - t))⁻¹) ^ e := by
  have he : (Real.sqrt (1 - t)) ^ e = (1 - t) ^ ((e : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul ht]
    congr 1
    ring
  simp only [factor, one_div, inv_zpow, he]

/-- Analytic Taylor data accompanies the numerical estimate. -/
theorem remainder_isBigO (e : ℤ) (n : ℕ) :
    (fun t : ℝ => factor e t - truncated e n t) =O[𝓝 0]
      (fun t : ℝ => |t| ^ n) := by
  simpa [truncated] using
    (factor_series e).hasFPowerSeriesAt.isBigO_sub_partialSum_pow n

/-- One exponent has a single constant valid for every truncation order on
the fixed closed half-radius interval. -/
theorem exponent_remainder (e : ℤ) :
    ∃ C > 0, ∀ t : ℝ, |t| ≤ 1 / 2 → ∀ n : ℕ,
      |factor e t - truncated e n t| ≤ C * ((4 / 3 : ℝ) * |t|) ^ n := by
  obtain ⟨a, ha, C, hC, hbound⟩ :=
    (factor_series e).uniform_geometric_approx'
      (r' := (3 / 4 : ℝ≥0)) (by exact ENNReal.coe_lt_coe.mpr (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro t ht n
  have htball : t ∈ Metric.ball (0 : ℝ) (3 / 4 : ℝ≥0) := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    norm_num
    linarith
  have hbase : a * (|t| / (3 / 4 : ℝ)) ≤ (4 / 3 : ℝ) * |t| := by
    calc
      a * (|t| / (3 / 4 : ℝ)) ≤ 1 * (|t| / (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right ha.2.le (by positivity)
      _ = (4 / 3 : ℝ) * |t| := by ring
  calc
    |factor e t - truncated e n t|
        ≤ C * (a * (|t| / (3 / 4 : ℝ))) ^ n := by
          simpa [truncated] using hbound t htball n
    _ ≤ C * ((4 / 3 : ℝ) * |t|) ^ n := by
      have ha0 : 0 ≤ a := ha.1.le
      gcongr

/-- The same constant works for every allowed signed packet power. -/
theorem capped_remainder (cap : ℕ) :
    ∃ C > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ t : ℝ, |t| ≤ 1 / 2 → ∀ n : ℕ,
      |factor e t - truncated e n t| ≤ C * ((4 / 3 : ℝ) * |t|) ^ n := by
  classical
  choose B hB hbound using exponent_remainder
  let powers := Finset.Icc (-(cap : ℤ)) (cap : ℤ)
  have hsum : 0 ≤ ∑ e ∈ powers, B e :=
    Finset.sum_nonneg (fun e _ => (hB e).le)
  refine ⟨1 + ∑ e ∈ powers, B e, by linarith, ?_⟩
  intro e he t ht n
  have hmem : e ∈ powers := by
    exact Finset.mem_Icc.mpr (abs_le.mp he)
  have hle : B e ≤ 1 + ∑ j ∈ powers, B j := by
    have := Finset.single_le_sum (fun j _ => (hB j).le) hmem
    linarith
  exact (hbound e t ht n).trans
    (mul_le_mul_of_nonneg_right hle (by positivity))

/-- Substitution of the actual beta difference and coupling retains all
powers of delta and g. There is no coupling-dependent constant. -/
theorem unit_power_remainder (cap : ℕ) :
    ∃ C > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      |delta * g ^ 2| ≤ 1 / 2 → ∀ n : ℕ,
      |unit delta g ^ e - truncated e n (delta * g ^ 2)| ≤
        C * (4 / 3 : ℝ) ^ n * |delta| ^ n * |g| ^ (2 * n) := by
  obtain ⟨C, hC, hbound⟩ := capped_remainder cap
  refine ⟨C, hC, ?_⟩
  intro e he delta g hsmall n
  have hpos : 0 ≤ 1 - delta * g ^ 2 := by
    have := le_abs_self (delta * g ^ 2)
    linarith
  have hfactor := factor_eq_unit_power e (delta * g ^ 2) hpos
  have h := hbound e he (delta * g ^ 2) hsmall n
  rw [hfactor] at h
  calc
    |unit delta g ^ e - truncated e n (delta * g ^ 2)|
        ≤ C * ((4 / 3 : ℝ) * |delta * g ^ 2|) ^ n := h
    _ = C * (4 / 3 : ℝ) ^ n * |delta| ^ n * |g| ^ (2 * n) := by
      simp only [abs_mul, abs_pow, mul_pow, ← pow_mul]
      ring

/-- This coefficient multiplies only the new even coupling power 2*n. -/
def correctionCoefficient (e : ℤ) (delta g : ℝ) (n : ℕ) : ℝ :=
  (unit delta g ^ e - truncated e n (delta * g ^ 2)) / g ^ (2 * n)

def corrected (e : ℤ) (delta physical : ℝ) (n : ℕ) (g : ℝ) : ℝ :=
  truncated e n (delta * g ^ 2) + correctionCoefficient e delta physical n * g ^ (2 * n)

/-- The finite correction restores the entire scalar at the actual point. -/
theorem corrected_at_physical (e : ℤ) (delta physical : ℝ) (n : ℕ)
    (hphysical : physical ≠ 0) :
    corrected e delta physical n physical = unit delta physical ^ e := by
  rw [corrected, correctionCoefficient, div_mul_cancel₀ _ (pow_ne_zero _ hphysical)]
  ring

/-- The high-order interpolation coefficient is uniformly bounded as the
physical coupling tends to zero; no inverse physical-coupling loss remains. -/
theorem correctionCoefficient_bound (cap : ℕ) :
    ∃ C > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta physical : ℝ,
      physical ≠ 0 → |delta * physical ^ 2| ≤ 1 / 2 → ∀ n : ℕ,
      |correctionCoefficient e delta physical n| ≤
        C * (4 / 3 : ℝ) ^ n * |delta| ^ n := by
  obtain ⟨C, hC, hbound⟩ := unit_power_remainder cap
  refine ⟨C, hC, ?_⟩
  intro e he delta physical hphysical hsmall n
  rw [correctionCoefficient, abs_div, abs_pow]
  apply (div_le_iff₀ (pow_pos (abs_pos.mpr hphysical) (2 * n))).2
  exact hbound e he delta physical hsmall n

end YM.Integration.ActualBetaRemainder
end
