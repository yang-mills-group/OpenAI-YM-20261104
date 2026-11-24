import YM.Integration.CensusFusionRate
import YM.Integration.CensusFusionEnvelope

/-! Uniform purchase of the original hard allowance on the discarded
physical cluster, with the complete capped soft fusion charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CensusFusionPrice

open Filter Lattice Wilson RG RG.Shoot Marker Push.AbsoluteSums
open AnalyticBridge VerifiedReset Collection Quotes Residual Geo
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Currency FullQLocal FullQLocal.RenderedStep
open RG01Estimate Pert.Asymptotics Progress.DirectedRecipe Extra.Iteration
open WilsonLimitConstruction.FundedCensusVacuum
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

/-- The only inverse threshold in the zero-alpha soft fusion cost is
paired with the actual high-source price. -/
theorem soft_le (G : Gauge) (p : BudgetPoint) (c : Clip) {σ C H : ℝ}
    (hs : 0 < σ) (hH : 0 ≤ H) :
    0 ≤ CappedCensusFusion.soft G p c σ C H ∧
    CensusFusionEnvelope.block p.B * CappedCensusFusion.soft G p c σ C H ≤
      CensusFusionEnvelope.coefficient G p c σ C * (H/p.threshold) := by
  let r := CappedCensusFusion.radius σ
  have hr : 0 < r := lt_min (by linarith) zero_lt_one
  have hz : 0 ≤ (1-Real.exp (-r))⁻¹ := inv_nonneg.mpr <|
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.le))
  have hz1 : 0 ≤ (1-Real.exp (-(1:ℝ)))⁻¹ := inv_nonneg.mpr <|
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  have hLow : 0 ≤ CappedCensusFusion.low p c σ C := by
    change 0 ≤ Footprint.payment 1 p.B 0 r 1
      (Fintype.card Signed * lowerSize c C) (p.supportExponent+1) lowCount
    unfold Footprint.payment Footprint.degreeIncome lowerSize
    have hh := c.quadratic_pos
    have hsq : 0 ≤ C*C := mul_self_nonneg C
    positivity
  have hr0 : 0 ≤ softReset G p 1 := by
    unfold softReset Footprint.payment Footprint.degreeIncome
    have hl := loss_pos G p
    positivity
  have hrH : softReset G p H = softReset G p 1*H := by
    unfold softReset Footprint.payment Footprint.degreeIncome; ring
  have hT : H ≤ H/p.threshold := (le_div_iff₀ p.threshold_pos).2
    (mul_le_of_le_one_right hH p.threshold_le)
  have hpair := pair_nonneg G p
  have hh : hitNeed p G 0 H = 2*(H/p.threshold)+H*(2:ℝ)⁻¹*pairBill G p := by
    unfold hitNeed
    rw [abs_zero,zero_add]
    field_simp [p.threshold_pos.ne']
  have hH0 : 0 ≤ H/p.threshold := div_nonneg hH p.threshold_pos.le
  have hhit : hitNeed p G 0 H ≤ (2+(2:ℝ)⁻¹*pairBill G p)*(H/p.threshold) := by
    rw [hh]
    linarith only [mul_le_mul_of_nonneg_right hT (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)⁻¹) hpair),
      show H*((2:ℝ)⁻¹*pairBill G p)=H*(2:ℝ)⁻¹*pairBill G p by ring,
      show (2+(2:ℝ)⁻¹*pairBill G p)*(H/p.threshold)=
        2*(H/p.threshold)+(H/p.threshold)*((2:ℝ)⁻¹*pairBill G p) by ring]
  have hB : 0 ≤ CensusFusionEnvelope.block p.B := by unfold CensusFusionEnvelope.block; positivity
  constructor
  · unfold CappedCensusFusion.soft
    rw [hrH,hh]
    positivity
  · unfold CappedCensusFusion.soft CensusFusionEnvelope.coefficient
    rw [hrH]
    calc
      _ ≤ CensusFusionEnvelope.block p.B *
          (softReset G p 1*(H/p.threshold)+
            ((2+(2:ℝ)⁻¹*pairBill G p)*(H/p.threshold))*CappedCensusFusion.low p c σ C) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hT hr0)
          (mul_le_mul_of_nonneg_right hhit hLow)) hB
      _ = _ := by ring

/-- One threshold before all cutoffs and torus periods buys the actual
nonlinear fusion rates using the income certificate's one-eighth gap. -/
theorem funded (R : Run G) (hG : G.Simple) (A : NumericSchedule R.family J)
    (hclip : ∀ᶠ m : ℕ in atTop, (R.family.path.levels.params m).clip.direct ≤ 1) :
    ∀ᶠ m : ℕ in atTop, ∀ N per : ℕ, m < N →
      let L := R.family.path.levels
      let q := A.outputNorm m
      let S := L.params m
      let H := (2*regulatorRun R.family N per (m+1))^(J.order+1)
      let γ := L.clock.forcedAllowance m
      ∀ w : ℝ, 0 ≤ w → w ≤ (1/8:ℝ)*γ →
        ∃ κ, Payments.Rates q.B γ w (CappedCensusFusion.soft G q S.clip S.width S.paths H) κ := by
  let L := R.family.path.levels
  let t : ℝ := (2:ℝ)^(J.order+1)
  obtain ⟨d,henv⟩ := CensusFusionEnvelope.eventual R hG A hclip
  have ht : 0 < t := pow_pos (by norm_num) _
  have hone := WilsonLimitConstruction.FundedSurplusPrice.cost_small R hG A 1
    (by norm_num) 0 1 1 (by norm_num) (by norm_num)
  have hpay := WilsonLimitConstruction.FundedSurplusPrice.cost_small R hG A (4*t)
    (by positivity) d 1 (1/32) (by norm_num) (by norm_num)
  have hsmall := WilsonLimitConstruction.FundedSurplusPrice.cost_small R hG A 8
    (by norm_num) d 1 1 (by norm_num) (by norm_num)
  have hadj := UnmarkedContractionAdmission.adjacent R hG 1 (T := 2) (by norm_num)
  filter_upwards [henv,hone,hpay,hsmall,hadj,StepRate.threshold_le_power L hG 1] with
    m he ho hprice hflat ha hh
  intro N per hN _ q S H γ w hw hin
  let f := regulatorRun R.family N per (m+1)
  let a := A.admittedCost m
  have hf : 0 < f := Currency.g_pos R.makes N per (m+1) (Nat.succ_le_of_lt hN)
  have hf1 : f ≤ 1 := by simpa only [pow_zero,Real.rpow_one,one_mul] using ho N per hN
  have hac : 0 ≤ a^d := pow_nonneg (A.admitted_cost_nonnegative m) _
  have hacut : f ≤ 2*regulatorRun R.family N per m := by
    simpa only [Real.rpow_one] using ha N per hN
  have hcoarse : regulatorRun R.family N per m ≤ 2*L.clock.hatCoupling m :=
    (Currency.hat_g R.makes N per m hN.le).2
  have hhat : L.clock.hatCoupling m ≤ L.clock.threshold m := WardBin.stepGle L m
  have hth : f ≤ 4*q.threshold := by
    change f ≤ 4*(A.outputNorm m).threshold
    rw [(A.output_norm m).threshold]
    change f ≤ 4*L.clock.threshold m
    linarith only [hacut,hcoarse,hhat]
  have hpow : f^(J.order+1) ≤ f^2 := pow_le_pow_of_le_one hf.le hf1
    (by have h := J.order_ge_two; omega : 2 ≤ J.order+1)
  have hH : 0 ≤ H := pow_nonneg (by change 0 ≤ 2*f; positivity) _
  have hHt : H/q.threshold ≤ 4*t*f := by
    apply (div_le_iff₀ q.threshold_pos).2
    calc
      H = t*f^(J.order+1) := by change (2*f)^(J.order+1) = _; rw [mul_pow]
      _ ≤ t*f^2 := mul_le_mul_of_nonneg_left hpow ht.le
      _ ≤ 4*t*f*q.threshold := by nlinarith only [mul_le_mul_of_nonneg_left hth (mul_nonneg ht.le hf.le)]
  have hcut : CensusFusionEnvelope.block q.B*CappedCensusFusion.soft G q S.clip S.width S.paths H ≤
      (1/32:ℝ) := by
    have h := (soft_le G q S.clip (C := S.paths) S.width_pos hH).2
    calc
      _ ≤ CensusFusionEnvelope.coefficient G q S.clip S.width S.paths*(H/q.threshold) := h
      _ ≤ a^d*(H/q.threshold) := mul_le_mul_of_nonneg_right he.1 (div_nonneg hH q.threshold_pos.le)
      _ ≤ a^d*(4*t*f) := mul_le_mul_of_nonneg_left hHt hac
      _ = (4*t)*a^d*f := by ring
      _ ≤ 1/32 := by simpa only [Real.rpow_one] using hprice N per hN
  have hb := (station R N per m hN).band
  have hγ : 0 < γ := StepRate.step_nonneg L m
  have hγf : γ ≤ 2*f := (StepRate.forced_le L m).trans
    ((by simpa only [pow_one] using hh : Real.sqrt γ ≤ L.clock.hatCoupling (m+1)).trans
      (StepRate.calibration L hb).2.2)
  have hflat' : 4*CensusFusionEnvelope.block q.B*γ ≤ 1 := by
    calc
      _ ≤ (4*a^d)*(2*f) := mul_le_mul (mul_le_mul_of_nonneg_left he.2 (by norm_num)) hγf hγ.le (by positivity)
      _ = 8*a^d*f := by ring
      _ ≤ 1 := by simpa only [Real.rpow_one] using hflat N per hN
  exact CensusFusionRate.rates q.B hγ hw hin (soft_le G q S.clip S.width_pos hH).1 hcut hflat'

end YM.Integration.CensusFusionPrice
end
