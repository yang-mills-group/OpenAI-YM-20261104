import YM.Integration.WilsonThermometerMixedTandemReading
import YM.Integration.WilsonThermometerMixedTapScalar

/-! Restoring the radii of all original faces after the two local returns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedWages
open Finset Marker QuadraticLocal WilsonGeometricSignedCapture
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

theorem shrink (c : (J).Mode → ℂ) (w : Fin 3 → ℝ) (hp : ∀j, 0 < w j) {z : ℝ}
    (one : 1 ≤ z) : weightBill c (Stoop.radius w z) ≤ z^3*weightBill c w := by
  have zp : 0 < z := zero_lt_one.trans_le one
  unfold weightBill
  rw [mul_sum]
  apply sum_le_sum
  intro s _
  have tally : Poly.toll (Stoop.radius w z) s = Poly.toll w s / z^(s.val.card) := by
    simp only [Poly.toll,Stoop.radius,Finset.prod_div_distrib,Finset.prod_const]
  rw [tally,div_div_eq_mul_div,mul_div_assoc]
  have size : s.val.card ≤ 3 := by simpa using card_le_univ s.val
  have tariff := pow_le_pow_right₀ one size
  have pos : 0 ≤ ‖c s‖ / Poly.toll w s := div_nonneg (norm_nonneg _) (Poly.worth hp _).le
  calc
    _ = z^(s.val.card)*(‖c s‖/Poly.toll w s) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right tariff pos

theorem chain (c : (J).Mode → ℂ) (w : Fin 3 → ℝ) (hp : ∀j, 0 < w j)
    {x r y : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) (hy : 1 ≤ y) :
    weightBill c (Stoop.radius (Stoop.radius (Stoop.radius w (x^6)) r) (y^6))
      ≤ (x^6*r*y^6)^3*weightBill c w := by
  have joint : Stoop.radius (Stoop.radius (Stoop.radius w (x^6)) r) (y^6) =
      Stoop.radius w (x^6*r*y^6) := by ext i; simp only [Stoop.radius,div_div]
  rw [joint]
  exact shrink c w hp (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) hr) (one_le_pow₀ hy))

theorem scaled (c : (J).Mode → ℂ) (w : Fin 3 → ℝ) (hp : ∀j, 0 < w j)
    {x r y g F : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) (hy : 1 ≤ y) (gp : 0 < g) (l : ℕ)
    (gap : g^2*x ≤ 2) (restore : g^2*r ≤ 4) (last : g^2*y ≤ 2)
    (paid : g^l*weightBill c w ≤ F) :
    g^(l+78)*weightBill c (Stoop.radius (Stoop.radius (Stoop.radius w (x^6)) r) (y^6)) ≤
      ((2:ℝ)^6*4*2^6)^3*F := by
  let z:=x^6*r*y^6
  have xn:=zero_le_one.trans hx
  have yn:=zero_le_one.trans hy
  have rn:=zero_le_one.trans hr
  have price : (g^2*x)^6*(g^2*r)*(g^2*y)^6 ≤ (2:ℝ)^6*4*2^6 :=
    mul_le_mul (mul_le_mul (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) xn) gap 6) restore
      (mul_nonneg (sq_nonneg _) rn) (by norm_num)) (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) yn) last 6)
      (pow_nonneg (mul_nonneg (sq_nonneg _) yn) _) (by norm_num)
  have bound : g^78*z^3 ≤ ((2:ℝ)^6*4*2^6)^3 := by
    rw [show g^78*z^3=((g^2*x)^6*(g^2*r)*(g^2*y)^6)^3 from by dsimp [z]; ring]
    exact pow_le_pow_left₀ (by positivity) price _
  have m0 : 0 ≤ weightBill c w := sum_nonneg fun s _ => div_nonneg (norm_nonneg _) (Poly.worth hp _).le
  calc
    _ ≤ g^(l+78)*(z^3*weightBill c w) :=
      mul_le_mul_of_nonneg_left (chain c w hp hx hr hy) (pow_nonneg gp.le _)
    _ = (g^78*z^3)*(g^l*weightBill c w) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul bound paid (mul_nonneg (pow_nonneg gp.le _) m0) (by norm_num)
end YM.Integration.WilsonThermometerMixedWages
end
