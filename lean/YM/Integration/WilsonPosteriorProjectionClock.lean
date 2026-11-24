import YM.Integration.WilsonPosteriorProjectionCoefficient

/-! The actual angular response grows by one inverse beta power per
derivative. Sampling at the fourth power of the original physical coupling
pays this cost at arbitrarily high degree and any fixed wire rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionClock
open Finset RG01.Kernel RG01.Kernel.Wheel
open WilsonPosteriorProjectionWireRoom WilsonPosteriorProjectionCoefficient
open scoped BigOperators Classical
variable {G : Gauge} {r : ℕ}

def ceiling (G : Gauge) (C : ℝ) (q d : ℕ) (u : Fin r → ℝ) :=
  ((1+C*tariff G)*(1+slots u))^q * (4:ℝ)^d *
    |compensation G q (invoice q 1) (1+2*1)|

private theorem linear (G : Gauge) (q : ℕ) (b : ℝ) :
    compensation G q (invoice q b) (1+2*1) = b * compensation G q (invoice q 1) (1+2*1) := by
  unfold compensation invoice
  ring

theorem debit (u : Fin r → ℝ) (q d : ℕ) (g y κ C : ℝ) (hg : 0<g) (g1 : g≤1)
    (hy : 0≤y) (ycap : y*g^2≤4) (hC : 0≤C) (penalty : |κ| * g^2 ≤ C) :
    response G κ (y^d) g q u * g^(2*q+2*d) ≤ ceiling G C q d u := by
  have tf : 0≤tariff G := zero_le_one.trans (fee G)
  have su : 0 ≤ slots u := sum_nonneg fun i _ => abs_nonneg (u i)
  have g2 : g^2≤1 := pow_le_one₀ hg.le g1
  have cost : (1+abs κ*tariff G)*g^2 ≤ 1+C*tariff G := by
    calc
      _ = g^2 + (abs κ*g^2)*tariff G := by ring
      _ ≤ _ := add_le_add g2 (mul_le_mul_of_nonneg_right penalty tf)
  have tariff : ((1+abs κ*RG01.Kernel.tariff G)*(1+abs g*slots u))*g^2 ≤
      (1+C*RG01.Kernel.tariff G)*(1+slots u) := by
    calc
      _ = ((1+abs κ*RG01.Kernel.tariff G)*g^2)*(1+abs g*slots u) := by ring
      _ ≤ _ := mul_le_mul cost (add_le_add le_rfl (mul_le_of_le_one_left su (by rwa [abs_of_pos hg])))
        (by positivity) (by positivity)
  unfold response ceiling
  rw [linear G q (y^d),abs_mul,abs_of_nonneg (pow_nonneg hy _)]
  calc
    _ = (((1+abs κ*RG01.Kernel.tariff G)*(1+abs g*slots u))*g^2)^q * (y*g^2)^d *
        |compensation G q (invoice q 1) (1+2*1)| := by
      simp only [mul_pow,pow_add,pow_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (by positivity) tariff q)
        (pow_le_pow_left₀ (by positivity) ycap d) (by positivity) (by positivity)) (abs_nonneg _)

theorem follows (u : Fin r → ℝ) (q d h : ℕ) (g y κ C : ℝ) (hg : 0<g) (g1 : g≤1)
    (hy : 0≤y) (ycap : y*g^2≤4) (hC : 0≤C) (penalty : |κ| * g^2 ≤ C)
    (order : 2*q+2*d+h+4*r ≤ 4*q) :
    response G κ (y^d) g q u * (g^4)^q ≤ ceiling G C q d u * g^(h+4*r) := by
  have tf : 0≤tariff G := zero_le_one.trans (fee G)
  have su : 0 ≤ slots u := sum_nonneg fun i _ => abs_nonneg (u i)
  have nn : 0≤response G κ (y^d) g q u := by unfold response; positivity
  calc
    _ = response G κ (y^d) g q u * g^(4*q) := by rw [pow_mul]
    _ ≤ response G κ (y^d) g q u * g^(2*q+2*d+h+4*r) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg.le g1 order) nn
    _ = (response G κ (y^d) g q u * g^(2*q+2*d))*g^(h+4*r) := by
      rw [show 2*q+2*d+h+4*r = (2*q+2*d)+(h+4*r) by omega,pow_add,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (debit u q d g y κ C hg g1 hy ycap hC penalty)
       (pow_nonneg hg.le _)

end YM.Integration.WilsonPosteriorProjectionClock

