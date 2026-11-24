import YM.Integration.WilsonEmittedOutputPower
/-! Price the full group values of the same compact and long original roster without varying its physical pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedGrossTariff
open Finset Lattice Wilson RG QuadraticLocal QuadraticLocal.Earn Push Push.AbsoluteSums Push.AbsoluteSums.Animals
open WilsonEmittedGroupWallet WilsonEmittedCompactTariff Real
open scoped BigOperators

def fixedCost : ℝ := Real.exp (102*1000)*9^4*4^4*(4:ℕ).factorial*5*2^13

theorem original (B:BudgetPoint) (s t m:ℕ) {H σ ζ b:ℝ} (H1:1<H) (logH:1≤Real.log H)
    (size:B.B=Nat.ceil ((Real.log H)^2)) (hs:(s:ℝ)≤Real.log H) (ht:(t:ℝ)≤Real.log H)
    (σ0:0<σ) (price:Real.exp ((σ⁻¹)^2)≤H) (width:strip σ≤ζ)
    (low:B.supportExponent+2≤102) (b0:0≤b) :
    stock B s t m b ζ ≤ b*fixedCost*H^217*Real.exp ζ := by
  let y:=1+Real.log H
  have y0:1≤y:=by unfold y;linarith
  have yH:y≤2*H:=by unfold y;linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans H1)]
  have small:0<strip σ:=lt_min zero_lt_one (div_pos σ0 (by norm_num))
  have ζ0:0<ζ:=small.trans_le width
  have w:ζ⁻¹≤4*y:=(inv_anti₀ small width).trans (reciprocal price)
  have e : 0<1-Real.exp (-strip σ):=sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr small))
  have big : 1-Real.exp (-(strip σ))≤1-Real.exp (-ζ):=sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg width)) _
  have gap:(1-Real.exp (-ζ))⁻¹≤5*y:=
    (denominator ζ0).trans (by linarith)
  have edge:(B.B:ℝ)≤y^2+1:=by
    rw [size];apply (Nat.ceil_lt_add_one (sq_nonneg (Real.log H))).le.trans;unfold y;nlinarith
  have radius:(((B.B+2)+(B.B+2)+1:ℕ):ℝ)≤9*y^2:=by
    have :=one_le_pow₀ y0 (n:=2);push_cast;linarith
  have spread:(Footprint.spread 1 (B.B+2):ℝ)≤9^4*y^8:=by
    simp only [Footprint.spread,one_mul,ballCost,Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) radius 4).trans_eq (by ring)
  have tax:Real.exp ((B.supportExponent+2)*Invoice.tax s t) ≤ Real.exp (102*1000)*H^204:=by
    calc
      _ ≤ Real.exp (102*(1000+Real.log H+Real.log H)):=by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul low (by unfold Invoice.tax;linarith) (by unfold Invoice.tax;positivity) (by norm_num)
      _ = Real.exp (102*1000)*H^204:=by
        rw [show (102:ℝ)*(1000+Real.log H+Real.log H)=102*1000+(204:ℕ)*Real.log H by ring,
          Real.exp_add,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans H1)]
  have tail:Real.exp (-ζ)^m≤1:=pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ζ0.le))
  have den:0≤(1-Real.exp (-ζ))⁻¹:=inv_nonneg.mpr (e.le.trans big)
  unfold stock Footprint.payment Footprint.degreeIncome
  simp only [mul_one,Nat.add_zero]
  calc
    _ ≤ Real.exp (102*1000)*H^204*b*(9^4*y^8)*
        ((4*y)^4*((4:ℕ).factorial:ℝ)*Real.exp ζ)*(5*y)*1:=by gcongr
    _ = b*(Real.exp (102*1000)*9^4*4^4*((4:ℕ).factorial:ℝ)*5)*H^204*y^13*Real.exp ζ:=by ring
    _ ≤ b*(Real.exp (102*1000)*9^4*4^4*((4:ℕ).factorial:ℝ)*5)*H^204*(2*H)^13*Real.exp ζ:=by gcongr
    _ = b*fixedCost*H^217*Real.exp ζ:=by unfold fixedCost;rw [mul_pow];ring

end YM.Integration.WilsonEmittedGrossTariff
end
