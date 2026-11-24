import YM.Integration.WilsonIndependentConditionedStoppedTill
import YM.Integration.WilsonReportingAbsoluteInletCoordinates

/-! The actual older thermal coupling fits the same stopping allowance on the booked optical collar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioClock
open Filter RG Lattice Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics XSpace
open Table Spec Climb Trace.Pilot PhysMS Extraction
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open private eventually_log from YM.Integration.WilsonReportingAbsoluteInletCoordinates
open scoped Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale

include simple in
theorem original (old:ℕ):∀ᶠ f:ℕ in atTop,∀{first v K N per:ℕ},first ≤ v→v ≤ f→f ≤ K→K ≤ N→
    σ K-σ first≤(old:ℝ)*(1+Real.log (β v)) →
    |regulatorRun R.family N per v| ≤ 8*thermal R f ∧ |regulatorRun R.family N per v| ≤ 1:=by
  have slope:0 ≤ G.slopeConstant:=(Gauge.slopeConstant_pos simple).le
  have late:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [late.eventually (eventually_log (2*G.slopeConstant*(old:ℝ)) (by positivity)),
    late.eventually_ge_atTop (64:ℝ),late.eventually_ge_atTop (Real.exp 1)] with f wage large logf
  intro first v K N per lower live upper top span
  let formal:=R.family.path.β N per v
  have vp:0<β v:=zero_lt_one.trans (R.family.path.levels.fits.delayed v)
  have fp:0<β f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have bp:0<formal:=Overlay.beta_positive R.makes.wilson (live.trans (upper.trans top))
  have raw:β v/2 ≤ formal:=(R.makes.wilson.represents N per v (live.trans (upper.trans top))).band.1
  have log_one:1 ≤ Real.log (β f):=by simpa using Real.log_le_log (Real.exp_pos 1) logf
  have log_le:Real.log (β v)≤Real.log (β f):=WilsonAdmissionScale.logarithm_monotone R.family.path.levels simple live
  have before:= (OPE.scale_mono R.family.S).monotone lower
  have after:= (OPE.scale_mono R.family.S).monotone upper
  have dt:σ f-σ v≤(old:ℝ)*(2*Real.log (β f)):=by
    refine (show σ f-σ v≤σ K-σ first by linarith).trans (span.trans ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have shift:β f-β v=G.slopeConstant*(σ f-σ v):=by
    change (_+_*(σ f))-(_+_*(σ v))=_
    ring
  have diff:=mul_le_mul_of_nonneg_left dt slope
  have small:β f-β v ≤ β f/2:=by
    rw [shift]
    change (2*G.slopeConstant*(old:ℝ))*Real.log (β f) ≤ β f/2 at wage
    linarith only [diff,wage]
  have comparison:β f ≤ 4*formal:=by linarith
  have root:=Real.sqrt_le_sqrt comparison
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num] at root
  change |(Real.sqrt formal)⁻¹| ≤ 8*(Real.sqrt (β f))⁻¹ ∧ |(Real.sqrt formal)⁻¹| ≤ 1
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr bp))]
  constructor
  · rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (Real.sqrt_pos.mpr bp) (Real.sqrt_pos.mpr fp),one_mul]
    linarith [Real.sqrt_nonneg formal]
  · have one:1 ≤ Real.sqrt formal:=by simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤formal by linarith)
    exact (inv_le_one₀ (Real.sqrt_pos.mpr bp)).mpr one

end YM.Integration.WilsonIndependentConditionedFolioClock
end
