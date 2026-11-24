import YangMills.WilsonProof.NativeSupport.JointPhysicalPush
import YangMills.WilsonProof.NativeSupport.JointPolynomialCalendar

/-! The two primitives bought on a particular actual blocking bond
represent respectively its temperature interpolation and the chosen
signed susceptibility direction. They can be installed on the same
forest-tagged bond and need no bound on a global density ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open scoped Classical
def thermalTest (h δ u:ℝ):ℝ := (Real.exp (-(δ*u))-1)/h
def directionTest (c σ u:ℝ):ℝ := σ*u/c

theorem thermal_unit {h δ c u:ℝ} (h0:0 < h) (h1:h ≤ 1) (u0:0 ≤ u) (uc:u ≤ c) (price:2*(|δ| *c) ≤ h) :
    ‖thermalTest h δ u‖ ≤ 1 := by
  have paid:2*(|δ| *u) ≤ h := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left uc (abs_nonneg δ)) zero_le_two).trans price
  have mag:|-(δ*u)|=|δ| *u:=by rw [abs_neg,abs_mul,abs_of_nonneg u0]
  have disk:|-(δ*u)| ≤ 1 := by rw [mag];linarith only [paid,h1,mul_nonneg (abs_nonneg δ) u0]
  rw [thermalTest,Real.norm_eq_abs,abs_div,abs_of_pos h0,div_le_one h0]
  exact (Real.abs_exp_sub_one_le disk).trans (by rwa [mag])

theorem direction_unit {c σ u:ℝ} (cp:0 < c) (charge:|σ| ≤ 1) (u0:0 ≤ u) (uc:u ≤ c) :
    ‖directionTest c σ u‖ ≤ 1 := by
  rw [directionTest,Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg u0,abs_of_pos cp,div_le_one cp]
  exact (mul_le_of_le_one_left u0 charge).trans uc

theorem tested_pair {h c:ℝ} (hp:0 < h) (cp:0 < c) (δ σ u z:ℝ) :
    (1+h*thermalTest h δ u)*(1+z*(h*c)*directionTest c σ u)=
      Real.exp (-(δ*u))*(1+z*h*σ*u) := by
  unfold thermalTest directionTest
  field_simp
  ring

def susceptibilityLoss (m W s ν:ℕ):ℕ:=4*radiusDegree W s ν*(m+1)
theorem terminal_price (m W s ν:ℕ) {x g:ℝ} (positive:0 < x) (band:x ≤ 4/g^2) :
    let h:=((x^radiusDegree W s ν)⁻¹)^2
    (h^(m+1))⁻¹ ≤ 4^(2*radiusDegree W s ν*(m+1))/g^(susceptibilityLoss m W s ν) := by
  intro h
  let d:=radiusDegree W s ν
  have invert:(h^(m+1))⁻¹=x^(2*d*(m+1)) := by
    dsimp only [h,d]
    simp only [←inv_pow,inv_inv,←pow_mul]
    congr 1
    ring
  rw [invert]
  have fee:= pow_le_pow_left₀ positive.le band (2*d*(m+1))
  refine fee.trans_eq ?_
  rw [div_pow,←pow_mul]
  congr 2
  dsimp only [susceptibilityLoss,d]
  ring

end YM.Integration.InletSusceptibility.Packet
