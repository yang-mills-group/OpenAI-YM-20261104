import YM.Integration.WilsonReceivedFirstQIncidence
import YM.Integration.WilsonReceivedClosePhysicalBirths

/-! Refund the literal once-issued Q radius. The price uses a fixed number of physical coupling powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseQOpeningPrice
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal PhysicalNext.Repeat.Legato Push
open Filter Finset Lattice RG Wilson QuadraticLocal.Advent
open Pert.Asymptotics PhysicalNext.Repeat.Legato

open Multi Exterior Push.PriceCompiler
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G)

theorem page (j:ℕ) : budgetR R j ≤ R.alloy.B.a.clock.hatBeta (j+1) := by
  have hot:1 ≤ R.alloy.B.a.clock.hatBeta (j+1) := (R.alloy.B.a.fits.delayed _).le
  exact (min_le_right _ _).trans ((Real.rpow_le_rpow_of_exponent_le hot
    (show Beaming.grain (R.alloy.B.a.clock.J j) ≤ 1 by unfold Beaming.grain; apply (div_le_one (by positivity)).2; simp)).trans_eq (Real.rpow_one _))

theorem two_upper (simple:G.Simple) {j N per:ℕ} (jN:j≤N)
    (clock:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose≤j) :
    R.alloy.B.a.clock.hatBeta ((j+1)+1) * (regulatorRun R.family N per j)^2 ≤ 8 := by
  have one := (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec j clock
  have two := (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec (j+1) (clock.trans (Nat.le_succ j))
  let β := R.family.path.β N per j
  have lower : R.alloy.B.a.clock.hatBeta j/2 ≤ β := (R.makes.wilson.represents N per j jN).band.1
  have pos:0<β := (half_pos (zero_lt_one.trans (R.alloy.B.a.fits.delayed j))).trans_le lower
  change R.alloy.B.a.clock.hatBeta ((j+1)+1)*(Real.sqrt β)⁻¹^2 ≤ 8
  rw [inv_pow,Real.sq_sqrt pos.le,←div_eq_mul_inv,div_le_iff₀ pos]
  linarith only [one,two,lower]

theorem demand {q:ℕ} {bill h g:ℝ} (h₁:1≤h) (g₀:0≤g)
    (retired:bill≤2*(3*g)^(q+1)) (late:(2*(3:ℝ)^(q+1))*g≤1) :
    max (h⁻¹*bill) (g^q)=g^q := by
  apply max_eq_right
  have pos:0≤2*(3*g)^(q+1) := by positivity
  have capped := (mul_le_mul_of_nonneg_left retired (inv_nonneg.mpr (zero_le_one.trans h₁))).trans
    (mul_le_of_le_one_left pos (inv_le_one_of_one_le₀ h₁))
  apply capped.trans
  calc 2*(3*g)^(q+1) = ((2*(3:ℝ)^(q+1))*g)*g^q := by rw [mul_pow];ring
       _ ≤ 1*g^q := mul_le_mul_of_nonneg_right late (pow_nonneg g₀ q)
       _ = _ := one_mul _

theorem radius {w T heat g:ℝ} (d:ℕ) (wp:0<w) (Tp:0<T) (hp:0<heat) (gp:0<g)
    (clock:heat*g^2≤8) (priced:1/(T*heat^d)≤w) :
    w⁻¹≤(T*8^d)*(g⁻¹)^(2*d) := by
  have H : heat ≤ 8*(g⁻¹)^2 := by
    rw [inv_pow,←div_eq_mul_inv,le_div_iff₀ (sq_pos_of_pos gp)]
    exact clock
  have pos:0<T*heat^d := mul_pos Tp (pow_pos hp _)
  have invw : w⁻¹ ≤ T*heat^d := (inv_le_iff_one_le_mul₀ wp).2 <| by
    have h:1 ≤ w*(T*heat^d) := (div_le_iff₀ pos).1 priced
    simpa only [mul_comm] using h
  apply invw.trans
  calc T*heat^d ≤ T*(8*(g⁻¹)^2)^d :=
         mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le H _) Tp.le
       _ = _ := by rw [mul_pow,pow_mul];ring
end YM.Integration.WilsonReceivedCloseQOpeningPrice
