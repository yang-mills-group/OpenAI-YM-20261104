import YM.Next.WARD_BIN.Hats
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Highway

/-!
# Absolute-cluster radius to actual coupling

The valuation for truncating cluster sums (before expanding individual vertices) is not a
canonical perturbative grading. The convergence estimate uses radius D growing like g^(-3/4).
All estimates will be translated to g from the actual fine Rep beta in band, not the calendar
hat. All estimates hold at fixed finite order. No dependence on the period or on staying a
bounded number of steps from the cutoff.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.StepRate

open Function Filter Lattice Schedule Wilson RG Pressure MeasureTheory
open Push Push.AbsoluteSums SectorMeasure Oriented Shoot Precision
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open PriceCompiler Org Input Supply Time
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6
open scoped Topology BigOperators Classical

variable {G : Gauge} (T : Levels G) (hG : G.Simple)

section
include hG

lemma price_next : ∀ᶠ i in atTop, T.clock.hatBeta (i+1) ≤ 2 * T.clock.hatBeta i := by
  have hg : 0 ≤ G.slopeConstant := (Gauge.slopeConstant_pos hG).le
  filter_upwards [T.S.divergent.eventually (eventually_gt_atTop 0),
    T.fits.mesh.eventually (gt_mem_nhds (show (0:ℝ) < 1 from zero_lt_one))] with i hi he
  change Real.log (T.S.block i).val / T.S.scale i < 1 at he
  rw [div_lt_iff₀ hi, one_mul] at he
  unfold Calendar.hatBeta
  rw [scale_succ]
  have hx:=mul_le_mul_of_nonneg_left he.le hg
  unfold Levels.S at hx
  linarith only [hx,T.clock.bar_pos]

/-- Divide the *coarse* seed budget and then pay arbitrary powers in fine units. -/
lemma threshold_flat (k : ℕ) :
    Tendsto (fun i => (T.clock.hatCoupling (i+1))⁻¹^k * Real.sqrt (T.clock.forcedAllowance i)) atTop (𝓝 0) := by
  have h : Tendsto (fun i => (2:ℝ)^k * ((T.clock.hatCoupling i)⁻¹^k * Real.sqrt (T.clock.forcedAllowance i))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (WardBin.pale T hG k).const_mul ((2:ℝ)^k)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · apply Eventually.of_forall; intro i
    exact mul_nonneg (pow_nonneg (inv_pos.mpr (WardBin.stepG T _)).le _) (Real.sqrt_nonneg _)
  filter_upwards [price_next T hG] with i hi
  have hc : (T.clock.hatCoupling (i+1))⁻¹ ≤ 2 * (T.clock.hatCoupling i)⁻¹ := by
    simp only [Calendar.hatCoupling, inv_inv]
    have hx := T.fits.delayed i; have hy := T.fits.delayed (i+1)
    have he := Real.sq_sqrt (show 0 ≤ T.clock.hatBeta (i+1) by linarith)
    have hh := Real.sq_sqrt (show 0 ≤ T.clock.hatBeta i by linarith)
    nlinarith only [he,hh,hi,Real.sqrt_nonneg (T.clock.hatBeta (i+1)), Real.sqrt_nonneg (T.clock.hatBeta i), hx, hy]
  rw [← mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_pos.mpr (WardBin.stepG T _)).le hc _) (Real.sqrt_nonneg _)

lemma threshold_le_power (k : ℕ) : ∀ᶠ i in atTop,
    Real.sqrt (T.clock.forcedAllowance i) ≤ T.clock.hatCoupling (i+1) ^ k := by
  filter_upwards [(threshold_flat T hG k).eventually (gt_mem_nhds zero_lt_one)] with i hi
  have hh := hi.le
  change (T.clock.hatCoupling (i+1))⁻¹^k * Real.sqrt (T.clock.forcedAllowance i) ≤ 1 at hh
  rw [inv_pow, mul_comm, ← div_eq_mul_inv, div_le_one (pow_pos (WardBin.stepG T _) _)] at hh
  exact hh
end

lemma allowance_le (k : ℕ) : T.clock.allowance k ≤ 1 := by
  unfold Calendar.allowance
  have hs := T.fits.delayed k
  have he := WardBin.stepGle T k
  have hk := T.fits.smallField k
  have ht : T.clock.hatCoupling k ≤ 1 := he.trans hk
  apply Real.rpow_le_one (WardBin.stepG T _).le ht
  norm_num

lemma step_nonneg (i : ℕ) : 0 < T.clock.forcedAllowance i := WardBin.force_pos ..
lemma forced_le (i : ℕ) : T.clock.forcedAllowance i ≤ Real.sqrt (T.clock.forcedAllowance i) := by
  have he := step_nonneg T i
  have hh : T.clock.forcedAllowance i ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    unfold Calendar.monitor
    apply neg_nonpos.mpr; positivity
  have hz := Real.sq_sqrt he.le
  nlinarith [Real.sqrt_pos.mpr he]

lemma calibration {m : ℕ} {β : ℝ} (hb : β ∈ Shoot.band T m) :
    0 < β ∧ 0 < (Real.sqrt β)⁻¹ ∧ T.clock.hatCoupling m ≤ 2*(Real.sqrt β)⁻¹ := by
  have hs : Next.Scheduling.inBand (T.clock.hatBeta m) β := trial_in hb
  have hh := band_gap (T.clock.hatBeta m) β (WardBin.hot T m) hs
  have hy : T.clock.hatBeta m/2 ≤ β := hb.1
  have hβ : 0<β:= lt_of_lt_of_le (half_pos (WardBin.hot ..)) hy
  refine ⟨hβ, inv_pos.mpr (Real.sqrt_pos.mpr hβ),?_⟩
  have hk : T.clock.hatCoupling m / 2 ≤ (Real.sqrt β)⁻¹ := hh.1
  linarith only [hk]

include hG in
lemma threshold_fine_divisor (k : ℕ) : ∀ᶠ i in atTop, ∀ β ∈ Shoot.band T (i+1),
    T.clock.forcedAllowance i ≤ Real.sqrt (T.clock.forcedAllowance i) * ((2 * (Real.sqrt β)⁻¹)^k) := by
  filter_upwards [threshold_le_power T hG k] with i hi β hb
  have hk := (Real.sq_sqrt (step_nonneg T i).le).symm
  calc
    _ = Real.sqrt _ * Real.sqrt _ := hk.trans (sq ..)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hi.trans (pow_le_pow_left₀ (WardBin.stepG T _).le (calibration T hb).2.2 _)) (Real.sqrt_nonneg _)

variable {L : Side} {m : ℕ}

/-- Available weight-to-actual-g conversion. D is only a radius for cluster-length
estimates, permitting vertices with weaker per-step grades. Thus charge two extra degree
occurrences per final power. -/
lemma length_power (hp : T.clock.hatBeta (m+1) = betaF G (T.clock.hatBeta m) L) (n : ℕ)
    {β : ℝ} (hb : β ∈ Shoot.band T (m+1)) :
    (Height.grow G L (T.clock.hatBeta m) ^ (2*n))⁻¹ ≤ (2*(Real.sqrt β)⁻¹)^n := by
  let s:= T.clock.hatBeta (m+1)
  have hs : 1 ≤ s := (T.fits.delayed _).le
  have hv : Real.sqrt s ≤ Height.grow G L (T.clock.hatBeta m)^2 := by
    unfold Height.grow
    rw [← hp, Real.sqrt_eq_rpow]
    change s^(1/(2:ℝ)) ≤ (s^(3/8:ℝ))^ (2:ℕ)
    rw [← Real.rpow_two, ← Real.rpow_mul (zero_le_one.trans hs)]
    apply Real.rpow_le_rpow_of_exponent_le hs; norm_num
  rw [pow_mul, ← inv_pow]
  have hl:= inv_pos.mpr ((Real.sqrt_pos_of_pos (zero_lt_one.trans_le hs)).trans_le hv)
  exact pow_le_pow_left₀ hl.le ((inv_anti₀ (Real.sqrt_pos_of_pos (zero_lt_one.trans_le hs)) hv).trans (calibration T hb).2.2) _

include hG in
lemma exponent_pays (k : ℕ) : ∀ᶠ m : ℕ in atTop, ∀ L : Side,
    T.clock.hatBeta (m+1)=betaF G (T.clock.hatBeta m) L →
    ∀ e : ℝ, Real.exp (-e) * T.clock.hatCoupling (m+1) ≤ T.clock.forcedAllowance m →
      Height.grow G L (T.clock.hatBeta m) ^ k ≤ Real.exp e := by
  filter_upwards [threshold_le_power T hG (k+1)] with m hm L hL e he
  let s:= T.clock.hatBeta (m+1)
  let t:= T.clock.hatCoupling (m+1)
  let r:= Height.grow G L (T.clock.hatBeta m)
  have hp : 0<t:= WardBin.stepG T _
  have hs : 1 ≤ s:= (T.fits.delayed _).le
  have hv : r ≤ t⁻¹ := by
    change Height.grow G L _ ≤ ((Real.sqrt s)⁻¹)⁻¹
    rw [inv_inv, Real.sqrt_eq_rpow, Height.grow, ← hL]
    exact Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
  have hx : 0 ≤ r := by unfold r Height.grow; rw [← hL]; exact Real.rpow_nonneg (zero_le_one.trans hs) _
  have he' : Real.exp (-e) ≤ t^k := le_of_mul_le_mul_right ((he.trans ((forced_le T m).trans hm)).trans_eq (pow_succ ..)) hp
  calc
    _ ≤ t⁻¹^k := pow_le_pow_left₀ hx hv _
    _ = (t^k)⁻¹ := (inv_pow ..)
    _ ≤ (Real.exp (-e))⁻¹ := inv_anti₀ (Real.exp_pos _) he'
    _ = _ := by rw [Real.exp_neg]; simp

end YM.RG01Estimate.StepRate
