import YM.Integration.WilsonOriginalUniformHighFourier

/-! the high-frequency physical bound after the derivative and the
absolute integer lattice weight have both been charged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHighModeExpense
open Filter
open scoped Topology

theorem spend (p j b : ℕ) {s u x A : ℝ} (hs : 1 ≤ s) (hu : 0 < u)
    (hsu : 1 ≤ s*u) (hx : 0 ≤ x) (paid : s^(p+12*(j+b))*x ≤ A) :
    (s^12)^j * x * (1+s^12)^b ≤ (2:ℝ)^b*A*u^p := by
  have hs0 := zero_le_one.trans hs
  have h12 : (1:ℝ) ≤ s^12 := one_le_pow₀ hs
  have hsum : 1+s^12 ≤ 2*s^12 := by linarith
  have h : s^p*((s^12)^j*(s^12)^b)*x ≤ A := by simpa [pow_add,pow_mul] using paid
  have up : 1 ≤ s^p*u^p := by rw [← mul_pow];exact one_le_pow₀ hsu
  have scaled : (s^12)^j*x*(s^12)^b ≤ A*u^p := calc
    _ ≤ ((s^12)^j*x*(s^12)^b)*(s^p*u^p) := le_mul_of_one_le_right (by positivity) up
    _ = (s^p*((s^12)^j*(s^12)^b)*x)*u^p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (pow_nonneg hu.le _)
  calc
    _ ≤ (s^12)^j*x*(2*s^12)^b :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum _) (by positivity)
    _ = (2:ℝ)^b*((s^12)^j*x*(s^12)^b) := by rw [mul_pow];ring
    _ ≤ _ := by rw [mul_assoc ((2:ℝ)^b)];exact mul_le_mul_of_nonneg_left scaled (by positivity)

theorem original (p j d : ℕ) (A D c : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ u : ℝ, 0 < u → 1 ≤ s*u →
      (s^12)^j*(A*(u⁻¹)^2*Real.exp (D*(u⁻¹)^4-c*s^6*u))*(1+s^12)^(2*d)
        ≤ (2:ℝ)^(2*d)*ε*u^p := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    WilsonOriginalUniformHighFourier.original (p+12*(j+2*d)) A D c hA hD hc hε]
      with s hs income u hu hsu
  exact spend p j (2*d) hs hu hsu (by positivity) (income u hu hsu)

end YM.Integration.WilsonOriginalHighModeExpense

