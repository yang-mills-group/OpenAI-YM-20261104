import YM.Integration.WilsonThermometerMixedThermal

/-! A fixed thermal change for the full signed endpoint at the genuine two adjacent dates. -/
set_option autoImplicit false
namespace YM.Integration.WilsonThermometerMixedFlatPrice
theorem paid {gt gs W F δ M : ℝ} (alive : 0 < gt) (charged : 0 < gs)
    (near : gt ≤ 2*gs) (wealth : 0 ≤ W) (l : ℕ) (salary : gt^l*W ≤ M)
    (endpoint : δ ≤ W*(gs⁻¹)^87*F) :
    gt^(l+87)*δ ≤ M*(2:ℝ)^87*|F| := by
  have fare : gt^87*(gs⁻¹)^87 ≤ (2:ℝ)^87 := by
    rw [←mul_pow,←div_eq_mul_inv]
    exact pow_le_pow_left₀ (div_nonneg alive.le charged.le) ((div_le_iff₀ charged).mpr near) _
  have loose : δ ≤ W*(gs⁻¹)^87*|F| := endpoint.trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg wealth (by positivity)))
  calc
    _ ≤ gt^(l+87)*(W*(gs⁻¹)^87*|F|) := mul_le_mul_of_nonneg_left loose (pow_nonneg alive.le _)
    _ = ((gt^l*W)*(gt^87*(gs⁻¹)^87))*|F| := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul salary fare (by positivity)
      ((mul_nonneg (pow_nonneg alive.le _) wealth).trans salary)) (abs_nonneg _)
end YM.Integration.WilsonThermometerMixedFlatPrice
