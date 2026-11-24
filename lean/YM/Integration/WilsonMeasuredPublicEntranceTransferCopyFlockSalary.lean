import YM.Integration.WilsonOriginalPublicTrialPhaseFlock
import YM.Integration.WilsonCapturedPrimaryMasterEarlierHeat

/-! The exact terminal money of the height-zero copied Wilson field at its fixed receiver. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyFlockSalary
open Function Filter Real Lattice RG Wilson Source Labels MergeProof MergeProof.Accent
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign

open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "S" => R.family.S
local notation "σ" => G.slopeConstant

include simple in
/-- The original grouped allowance can consume an exponentially growing inverse salary. -/
theorem original (u q:ℕ):
    ∀ᶠ c:ℕ in atTop,∀ f:ℕ,H f≤2*H c→∀ w:ℝ,0<w→w⁻¹≤Real.exp (H c/(10*σ)) →
      (WilsonOriginalPublicTrialPhaseRay.weight (S) (4*bling R.family.path.levels c*w⁻¹) c u)⁻¹≤1/(H f)^q:=by
  let b:ℝ:=2+4*(q:ℝ)
  let d:=Real.log (4*WilsonOriginalPublicTrialPhaseRay.unit)+(2/5:ℝ)*H u/σ
  have slope:0<σ:=Gauge.slopeConstant_pos simple
  have up:0<WilsonOriginalPublicTrialPhaseRay.unit:=WilsonOriginalPublicTrialPhaseRay.unit_pos
  have late:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [RG01.Physical.nextHat simple R.family.path.levels,
    late.eventually_ge_atTop ((10*σ*b)^2),late.eventually_ge_atTop (10*σ*d)] with c nearby scale base
  intro f compare w _ salary
  have hc:0≤H c:=zero_le_one.trans (R.family.path.levels.fits.delayed c).le
  have hf:0<H f:=zero_lt_one.trans_le (R.family.path.levels.fits.delayed f).le
  have sc:0≤Real.sqrt (H c):=Real.sqrt_nonneg _
  have square:=Real.sq_sqrt hc
  have root (x:ℝ)(le:x≤2*H c):Real.sqrt x≤2*Real.sqrt (H c):=by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity,?_⟩
    nlinarith only [le,square,hc]
  have logf:Real.log (H f)≤4*Real.sqrt (H c):=calc
    _=Real.log ((Real.sqrt (H f))^2):=by rw [Real.sq_sqrt hf.le]
    _=2*Real.log (Real.sqrt (H f)):=by rw [Real.log_pow];norm_num
    _≤2*Real.sqrt (H f):=mul_le_mul_of_nonneg_left (Real.log_le_self (Real.sqrt_nonneg _)) (by norm_num)
    _≤_:=by linarith only [root _ compare]
  have budget : b*Real.sqrt (H c)≤H c/(10*σ):=by
    apply (le_div_iff₀ (by positivity:0<10*σ)).2
    have h:=mul_le_mul_of_nonneg_right (Real.le_sqrt_of_sq_le scale) sc
    nlinarith only [h,square]
  have onset : d≤H c/(10*σ):=(le_div_iff₀ (by positivity)).2 (mul_comm d _ ▸ base)
  have change:H u-H c=σ*((S).scale u-(S).scale c):=by
    change (_+σ*(S).scale u)-(_+σ*(S).scale c)=_
    ring
  have ratio:Real.log ((S).a c/(S).a u)=(H u-H c)/σ:=by
    rw [WilsonReflectedRelativeDate.ratio,change]
    field_simp
  have money:
      Real.log (4*WilsonOriginalPublicTrialPhaseRay.unit)+Real.log ((S).a c/(S).a u)*(2/5:ℝ)+Real.sqrt (H (c+1))+H c/(10*σ)
      ≤-(q:ℝ)*Real.log (H f):=by
    rw [ratio]
    have positive:(0:ℝ)≤q:=by positivity
    have paid:=add_le_add (root _ nearby) (mul_le_mul_of_nonneg_left logf positive)
    have expense:Real.sqrt (H (c+1))+(q:ℝ)*Real.log (H f)≤b*Real.sqrt (H c):=by
      dsimp [b];nlinarith only [paid]
    dsimp only [d] at onset
    have slack:0≤H c/σ:=div_nonneg hc slope.le
    simp only [div_eq_mul_inv,mul_inv_rev] at onset budget expense slack ⊢
    ring_nf at onset budget expense slack ⊢
    linarith only [onset,budget,expense,slack]
  have scalePos:0<(S).a c/(S).a u:=div_pos ((S).a_pos _) ((S).a_pos _)
  calc
    _ = (4*WilsonOriginalPublicTrialPhaseRay.unit)*(((S).a c/(S).a u)^(2/5:ℝ)*Real.exp (Real.sqrt (H (c+1)))*w⁻¹):=by
      rw [WilsonOriginalPublicTrialPhaseRay.weight,inv_inv,WilsonOriginalPublicTrialPhaseRace.wage,bling]
      ring
    _ ≤ (4*WilsonOriginalPublicTrialPhaseRay.unit)*(((S).a c/(S).a u)^(2/5:ℝ)*Real.exp (Real.sqrt (H (c+1)))*Real.exp (H c/(10*σ))):=by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left salary (by positivity)) (by positivity)
    _ = Real.exp (Real.log (4*WilsonOriginalPublicTrialPhaseRay.unit)+Real.log ((S).a c/(S).a u)*(2/5:ℝ)+Real.sqrt (H (c+1))+H c/(10*σ)):=by
      rw [Real.rpow_def_of_pos scalePos];simp only [Real.exp_add,Real.exp_log (by positivity:0<4*WilsonOriginalPublicTrialPhaseRay.unit)];ring
    _ ≤ Real.exp (-(q:ℝ)*Real.log (H f)):=Real.exp_le_exp.mpr money
    _ = _ := by rw [neg_mul,Real.exp_neg,← Real.log_pow,Real.exp_log (pow_pos hf _),one_div]

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyFlockSalary
end
