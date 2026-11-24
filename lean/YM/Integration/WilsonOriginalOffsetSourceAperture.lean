import YM.Integration.WilsonOriginalOffsetSingletonSource
import YM.Integration.WilsonOriginalStarPrintedRead

/-! One restored singleton aperture on the original intermediate torus.
The radius and retained-support cutoff use the reporting budget at this date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOffsetSourceAperture
open Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Tint
open WilsonRetainedMarkedInletRegular WilsonOriginalDepositedRegularHearing
open scoped Classical BigOperators

variable {G : Gauge} {n : Side}
def cutoff (P : Rep G n) (K δ : ℝ) : ℕ :=
  ⌈Real.log ((1+K)/δ)/P.p.supportExponent⌉₊

def radius (P : Rep G n) (K δ : ℝ) : ℝ :=
  (2*max 1 (Real.exp (3*(cutoff P K δ:ℝ))*cost P.p)*(1+K))⁻¹

theorem restored (P : Rep G n) {K δ : ℝ} (cap : 0≤K) (pos : 0<δ) (unit : δ≤1) :
    let D := cutoff P K δ
    let w := radius P K δ
    0<w ∧ w*K≤1/2 ∧ Real.exp (3*(D:ℝ))*cost P.p*(w*K)≤1/2 ∧
      fee P D K≤δ ∧ w⁻¹≤2*(1+K)*max 1
        (Real.exp 3 * ((1+K)/δ)^(3/P.p.supportExponent)*cost P.p) := by
  let D := cutoff P K δ
  let F := Real.exp (3*(D:ℝ))*cost P.p
  let L := max 1 F
  let u := radius P K δ
  have ck : 0<1+K := by linarith
  have ok : 1 ≤ (1+K)/δ := (le_div_iff₀ pos).mpr (by linarith)
  have a := P.p.exponent_pos
  have high : Real.log ((1+K)/δ) ≤ (D:ℝ)*P.p.supportExponent :=
    (div_le_iff₀ a).mp (Nat.le_ceil _)
  have low : (D:ℝ)<Real.log ((1+K)/δ)/P.p.supportExponent+1 :=
    Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg ok) a.le)
  have lp : 0<L := zero_lt_one.trans_le (le_max_left ..)
  have wp : 0<u := inv_pos.mpr (mul_pos (mul_pos (by norm_num) lp) ck)
  have cancel : L*(u*(1+K))=1/2 := by
    change L*((2*L*(1+K))⁻¹*(1+K))=1/2
    field_simp [lp.ne',ck.ne']
  have priced : L*(u*K)≤1/2 := by
    rw [←cancel]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) wp.le) lp.le
  have decay : Real.exp (-P.p.supportExponent*(D:ℝ)) ≤ ((1+K)/δ)⁻¹ := by
    rw [← Real.exp_log (zero_lt_one.trans_le ok), ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith
  have exit : fee P D K ≤ δ := by
    unfold fee
    have paid := mul_le_mul_of_nonneg_right decay cap
    apply paid.trans
    rw [inv_div,mul_comm,←mul_div_assoc]
    apply (div_le_iff₀ ck).mpr
    nlinarith
  have growth : F ≤ Real.exp 3*((1+K)/δ)^(3/P.p.supportExponent)*cost P.p := by
    have cp : 0 ≤ cost P.p := by unfold cost; positivity
    apply mul_le_mul_of_nonneg_right _ cp
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le ok),←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have u := (lt_div_iff₀ a).mp (show (D:ℝ)-1 < Real.log ((1+K)/δ)/P.p.supportExponent by linarith)
    field_simp [a.ne']
    nlinarith
  refine ⟨wp, (le_mul_of_one_le_left (mul_nonneg wp.le cap) (le_max_left 1 F)).trans priced,
    (mul_le_mul_of_nonneg_right (le_max_right 1 F) (mul_nonneg wp.le cap)).trans priced,exit,?_⟩
  change (2*L*(1+K))⁻¹⁻¹≤_
  rw [inv_inv,mul_right_comm]
  exact mul_le_mul_of_nonneg_left (max_le_max_left _ growth) (by positivity)

end YM.Integration.WilsonOriginalOffsetSourceAperture
