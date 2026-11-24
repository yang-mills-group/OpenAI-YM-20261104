import YM.Integration.WilsonOriginalAnalyticFourierTail

/-! The high-frequency analytic bound at the physical temperature of a
single reading, uniformly over every frequency above its cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalUniformHighFourier
open Filter Topology

/-- With frequency size s^12, this bound uses the physical u directly
and is uniform over the entire high-frequency range s*u ≥ 1. -/
theorem original (k : ℕ) (A D c : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ s : ℝ in atTop, ∀ u : ℝ, 0 < u → 1 ≤ s*u →
      s^k * (A * (u⁻¹)^2 * Real.exp (D*(u⁻¹)^4 - c*s^6*u)) ≤ ε := by
  let a : ℝ := 1
  have ha : 0 < a := zero_lt_one
  have hca : 0 < c*a := mul_pos hc ha
  have small := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k+2)).const_mul (A/a^2)
  rw [mul_zero] at small
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((D/a^4+1)/(c*a)),(tendsto_order.mp small).2 ε hε] with s hs1 height tail u hu hau
  have hu' : 0 < u := hu
  have h0 : 0 ≤ s := zero_le_one.trans hs1
  have hi : u⁻¹ ≤ s/a := (le_div_iff₀ ha).2 (calc
    u⁻¹*a ≤ u⁻¹*(s*u) := mul_le_mul_of_nonneg_left hau (inv_nonneg.mpr hu'.le)
    _ = s := by field_simp)
  have income : D/a^4 + 1 ≤ c*a*s := by simpa only [mul_comm s] using (div_le_iff₀ hca).1 height
  have exponent : D*(u⁻¹)^4 - c*s^6*u ≤ -s := by
    have positive := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hu'.le) hi 4) hD
    have spend : (D/a^4+1)*s^4 ≤ c*s^6*u := calc
      _ ≤ c*a*s*s^4 := mul_le_mul_of_nonneg_right income (pow_nonneg h0 _)
      _ = (c*s^5)*a := by ring
      _ ≤ (c*s^5)*(s*u) := mul_le_mul_of_nonneg_left hau (mul_nonneg hc.le (pow_nonneg h0 _))
      _ = c*s^6*u := by ring
    have sc : s ≤ s^4 := by calc
      s = s^1 := (pow_one _).symm
      _ ≤ s^4 := pow_le_pow_right₀ hs1 (by decide)
    rw [div_pow] at positive
    linarith only [positive,spend,sc,mul_comm (D/a^4+1) (s^4),
      show D*(s^4/a^4)=(D/a^4)*s^4 by ring]
  have expFee := Real.exp_le_exp.mpr exponent
  change s^k*(A*(u⁻¹)^2*Real.exp _) ≤ ε
  calc
    _ ≤ s^k*(A*(s/a)^2*Real.exp (-s)) := mul_le_mul_of_nonneg_left
      (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hu'.le) hi 2) hA)
        expFee (Real.exp_nonneg _) (mul_nonneg hA (sq_nonneg _))) (pow_nonneg h0 _)
    _ = (A/a^2)*(s^(k+2)*Real.exp (-s)) := by rw [pow_add,div_pow]; ring
    _ ≤ ε := tail.le

end YM.Integration.WilsonOriginalUniformHighFourier

