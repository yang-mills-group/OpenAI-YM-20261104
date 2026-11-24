import YM.Integration.WilsonEmittedLengthWindow
import YM.Integration.WilsonEmittedLocatedCensus

/-! The same original healthy earned roster can be read at a bounded spatial width.
Its whole compact derivative fare is a polynomial in the log of the physical budget
with a coefficient fixed by the selected order, independent of regulators and old radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedCompactTariff
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push.AbsoluteSums Push.AbsoluteSums.Animals Filter Real WilsonEmittedLocatedCensus WilsonEmittedRootSalary
open scoped BigOperators

def strip (σ:ℝ):=min 1 (σ/4)

theorem purchased {B:BudgetPoint} {K a g σ θ:ℝ}
    (paid:Invoice.Supports B K a g σ θ) (placed:a*(B.B:ℝ)⁻¹ ≤ σ/2) :
    Invoice.Supports B K a g σ (strip σ) := by
  obtain ⟨hg,h1,hK,ht,hσ,ha,he,hwidth⟩:=paid
  have gr:0<σ:=by linarith [mul_nonneg ha (inv_nonneg.mpr (Nat.cast_nonneg B.B))]
  refine ⟨hg,h1,hK,ht,hσ,ha,lt_min zero_lt_one (by positivity),?_⟩
  linarith [show strip σ≤σ/4 from min_le_right ..]

theorem reciprocal {σ x:ℝ} (h:Real.exp ((σ⁻¹)^2)≤x) :
    (strip σ)⁻¹ ≤ 4*(1+Real.log x) := by
  have hs:(σ⁻¹)^2≤Real.log x:=by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) h
  have ag:0≤Real.log x:=(sq_nonneg _).trans hs
  unfold strip
  by_cases z:1≤σ/4
  · rw [min_eq_left z,inv_one];linarith
  · rw [min_eq_right (le_of_not_ge z),inv_div,div_eq_mul_inv];nlinarith [sq_nonneg (σ⁻¹-1)]

theorem denominator {θ:ℝ}(pos:0<θ) : (1-Real.exp (-θ))⁻¹ ≤ 1+θ⁻¹ := by
  have q:0<1-Real.exp (-θ):=sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr pos))
  rw [←one_div,(div_le_iff₀ q)]
  rw [Real.exp_neg]
  field_simp
  linarith [Real.add_one_le_exp θ]

def fixed (G:Gauge) (J s pieces:ℕ) :=
  Real.exp (102*Invoice.tax s pieces)*fee G J s*9^4*4^(4+J*s)*((4+J*s).factorial:ℝ)*Real.exp 1*5

theorem original {G:Gauge} {B:BudgetPoint} {a σ x b:ℝ} (J s pieces:ℕ) (hb:0≤b)
    (pos:0<σ) (cap:a≤102) (reserve:Real.exp ((σ⁻¹)^2)≤x)
    (square:B.B=Nat.ceil ((Real.log x)^2)) :
    receipt G B J s pieces 0 b a (strip σ) ≤ b*fixed G J s pieces*(1+Real.log x)^(13+J*s) := by
  set y:=1+Real.log x
  set θ:=strip σ
  have ag:0≤Real.log x:=by
    have hs:0≤(σ⁻¹)^2:=sq_nonneg _
    apply hs.trans; simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) reserve
  have hey:1≤y:=by dsimp [y];linarith
  have y0:0≤y:=zero_le_one.trans hey
  have yp:1≤y^2:=one_le_pow₀ hey
  have t0:0<θ:=lt_min zero_lt_one (div_pos pos (by norm_num))
  have t1:θ≤1:=min_le_left ..
  have bound: θ⁻¹≤4*y:=reciprocal reserve
  have gap: (1-Real.exp (-θ))⁻¹≤5*y:=(denominator t0).trans (by linarith)
  have edge:(B.B:ℝ)≤y^2+1:=by
    rw [square]
    apply (Nat.ceil_lt_add_one (sq_nonneg (Real.log x))).le.trans
    dsimp [y];nlinarith
  have edge₂:(((B.B+2)+(B.B+2)+1:ℕ):ℝ)≤9*y^2:=by push_cast; linarith
  have present:(Footprint.spread 1 (B.B+2):ℝ)≤9^4*y^8:=by
    simp only [Footprint.spread,one_mul,ballCost,Nat.cast_pow]
    calc
      _ ≤ (9*y^2)^4:=pow_le_pow_left₀ (Nat.cast_nonneg _) edge₂ _
      _ = _:=by ring
  have tag: Real.exp (a*Invoice.tax s pieces)≤Real.exp (102*Invoice.tax s pieces):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right cap (by unfold Invoice.tax;positivity))
  have positive:=fee_pos G J s
  have pw:=pow_le_pow_left₀ (inv_nonneg.mpr t0.le) bound (4+J*s)
  rw [mul_pow] at pw
  unfold receipt Footprint.payment Footprint.degreeIncome
  simp only [pow_zero,mul_one]
  calc
    _ ≤ Real.exp (102*Invoice.tax s pieces)*b*fee G J s*(9^4*y^8)*
         ((4^(4+J*s)*y^(4+J*s))*((4+J*s).factorial:ℝ)*Real.exp 1)*(5*y) := by
      have ep:0≤(1-Real.exp (-θ))⁻¹:=inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr t0.le)))
      have e1:=Real.exp_le_exp.mpr t1
      gcongr
    _ = _ := by unfold fixed; rw [show 13+J*s=8+(4+J*s)+1 by omega];simp only [pow_add,pow_one];ring

end YM.Integration.WilsonEmittedCompactTariff
