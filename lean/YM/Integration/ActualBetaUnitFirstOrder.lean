import YM.Integration.ActualBetaRemainder

/-! The actual beta-reset unit is uniformly close to one at first order in
`delta * g^2`. The same exponent-cap constant controls the physical factor
and its inverse, without a fixed multiplicative loss at zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualBetaUnitFirstOrder

open ActualBetaRemainder

private theorem truncated_one (e : ℤ) (t : ℝ) : truncated e 1 t = 1 := by
  simp [truncated_sum, coefficient]

private theorem abs_le_one_add {x d : ℝ} (h : |x - 1| ≤ d) : |x| ≤ 1 + d := by
  have ht := abs_add_le (x - 1) 1
  simp only [sub_add_cancel, abs_one] at ht
  linarith

/-- One constant, chosen from the exponent cap, controls every signed factor
on the original closed half-radius domain. -/
theorem unit_power_near_one (cap : ℕ) :
    ∃ D > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      |delta * g ^ 2| ≤ 1 / 2 →
      |unit delta g ^ e - 1| ≤ D * |delta * g ^ 2| := by
  obtain ⟨C, hC, hbound⟩ := unit_power_remainder cap
  refine ⟨C * (4 / 3 : ℝ), mul_pos hC (by norm_num), ?_⟩
  intro e he delta g hsmall
  have h := hbound e he delta g hsmall 1
  rw [truncated_one] at h
  calc
    |unit delta g ^ e - 1|
        ≤ C * (4 / 3 : ℝ) ^ 1 * |delta| ^ 1 * |g| ^ (2 * 1) := h
    _ = (C * (4 / 3 : ℝ)) * |delta * g ^ 2| := by
      simp only [pow_one, mul_one, abs_mul, abs_pow]
      ring

/-- The same first-order constant bounds both the original factor and its
inverse. There is no nonzero physical-coupling premise. -/
theorem unit_and_inverse_bounds (cap : ℕ) :
    ∃ D > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      |delta * g ^ 2| ≤ 1 / 2 →
      |unit delta g ^ e| ≤ 1 + D * |delta * g ^ 2| ∧
      |(unit delta g ^ e)⁻¹| ≤ 1 + D * |delta * g ^ 2| := by
  obtain ⟨D, hD, hbound⟩ := unit_power_near_one cap
  refine ⟨D, hD, ?_⟩
  intro e he delta g hsmall
  refine ⟨abs_le_one_add (hbound e he delta g hsmall), ?_⟩
  apply abs_le_one_add
  simpa only [zpow_neg] using
    hbound (-e) (by simpa only [abs_neg] using he) delta g hsmall

end YM.Integration.ActualBetaUnitFirstOrder
end
