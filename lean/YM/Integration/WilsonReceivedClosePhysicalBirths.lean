import YM.Integration.WilsonReceivedCloseBirthPrice
import YM.Integration.WilsonReceivedCloseEndpoint

/-! Inverse radii paid at the original Wilson upper and receiving curvature births. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedClosePhysicalBirths
open Filter Finset Lattice RG Wilson QuadraticLocal.Advent
open Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "H" => R.alloy.B.a.clock.hatBeta
local notation "B" => budgetR R

include simple in
theorem cool :
    ∀ᶠ j : ℕ in atTop, ∀ N per, j ≤ N → 0 < regulatorRun R.family N per j ∧
      3*regulatorRun R.family N per j ≤ 1 := by
  filter_upwards [(RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop (18:ℝ)] with j far N per jN
  let y := R.family.path.β N per j
  have base := (R.makes.wilson.represents N per j jN).band.1
  change H j / 2 ≤ y at base
  have yp : 0<y := by linarith only [base,far]
  have sq := Real.sq_sqrt yp.le
  have rt := Real.sqrt_nonneg y
  constructor
  · exact inv_pos.mpr (Real.sqrt_pos.mpr yp)
  · change 3*(Real.sqrt y)⁻¹ ≤ 1
    rw [←div_eq_mul_inv,div_le_one (Real.sqrt_pos.mpr yp)]
    nlinarith only [sq,rt,far,base]

include simple in
/-- The upper original Q pays its own fixed published source derivative once, including both radius changes. -/
theorem upper {j N per : ℕ} (top : j ≤ N)
    (clock : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ j)
    {h Ω stamp C f w : ℝ} (rank : ℕ) (C₁ : 1 ≤ C) (fp : 0 < f)
    (h₁ : 1 ≤ h) (hc : h ≤ (B (j+1))^6) (Ω₁ : 1 ≤ Ω) (oc : Ω ≤ B (j+1))
    (sc : stamp ≤ B (j+1))
    (birth : w = (f/(C*(H ((j+1)+1))^rank*Ω)/(max 1 (B j*stamp))/2)/h) :
    f ≤ ((B j)^2*(B (j+1))^7)^2 * (2*C*8^rank*((regulatorRun R.family N per j)⁻¹)^(2*rank))*w := by
  let y := R.family.path.β N per j
  have first := (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec j clock
  have second := (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec (j+1) (by omega)
  have lower := (R.makes.wilson.represents N per j top).band.1
  change H j/2 ≤ y at lower
  have hot := (R.alloy.B.a.fits.delayed j)
  have y₀ : 0<y := by linarith only [hot,lower]
  have H₀ : 0 < H ((j+1)+1) := zero_lt_one.trans (R.alloy.B.a.fits.delayed _)
  have warm : H ((j+1)+1) ≤ 8*y := by linarith only [first,second,lower]
  have bj := budget_pos (i:=j) R
  have bu := budget_pos (i:=j+1) R
  have jp : 0 < B j := zero_lt_one.trans_le bj
  have up : 0 < B (j+1) := zero_lt_one.trans_le bu
  let guard := max 1 (B j*stamp)
  have guardPos : 0<guard := zero_lt_one.trans_le (le_max_left _ _)
  have guardFee : guard ≤ B j*B (j+1) := max_le (one_le_mul_of_one_le_of_one_le bj bu)
    (mul_le_mul_of_nonneg_left sc jp.le)
  have cp : 0 < C := zero_lt_one.trans_le C₁
  have op : 0 < Ω := zero_lt_one.trans_le Ω₁
  have hp : 0 < h := zero_lt_one.trans_le h₁
  have wp : 0<w := by
    rw [birth]
    exact div_pos (div_pos (div_pos (div_pos fp (by positivity)) guardPos) (by norm_num)) hp
  have invoice : f = (C*(H ((j+1)+1))^rank*Ω)*guard*2*h*w := by
    rw [birth]
    change _ = _ * (((f/_)/guard/2)/h)
    field_simp [guardPos.ne',cp.ne',op.ne',hp.ne',H₀.ne']
  have firstFee : C*(H ((j+1)+1))^rank*Ω ≤ C*(8*y)^rank*B (j+1) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ H₀.le warm _) cp.le)
      oc op.le (by positivity)
  have entry : B j*(B (j+1))^8 ≤ ((B j)^2*(B (j+1))^7)^2 := by
    calc
      _ ≤ (B j)^4*(B (j+1))^14 := mul_le_mul
        (by simpa only [pow_one] using (pow_le_pow_right₀ bj (by decide : 1 ≤ 4)))
        (pow_le_pow_right₀ bu (by decide : 8 ≤ 14)) (by positivity) (by positivity)
      _ = _ := by ring
  have angular : (8*y)^rank = 8^rank*((regulatorRun R.family N per j)⁻¹)^(2*rank) := by
    change _ = 8^rank*((Real.sqrt y)⁻¹)⁻¹^(2*rank)
    rw [inv_inv,pow_mul,Real.sq_sqrt y₀.le,mul_pow]
  rw [invoice]
  apply mul_le_mul_of_nonneg_right _ wp.le
  calc
    _ ≤ (C*(8*y)^rank*B (j+1))*(B j*B (j+1))*2*(B (j+1))^6 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul firstFee guardFee guardPos.le (by positivity))
        (by norm_num)) hc hp.le (by positivity)
    _ = (B j*(B (j+1))^8)*(2*C*(8*y)^rank) := by ring
    _ ≤ ((B j)^2*(B (j+1))^7)^2*(2*C*(8*y)^rank) := mul_le_mul_of_nonneg_right entry (by positivity)
    _ = _ := by rw [angular]; ring

end YM.Integration.WilsonReceivedClosePhysicalBirths
