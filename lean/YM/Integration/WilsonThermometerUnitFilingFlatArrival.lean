import YM.Integration.WilsonThermometerUnitFilingWindowRates

/-! Every moving terminal of the purchased short window eventually admits each fixed finite Wick order. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatArrival
open Function Filter Finset MeasureTheory Real Lattice Wilson RG RG16
open PhysicalNext PhysicalNext.Repeat Legato Pert.Asymptotics
open Overlay OPE OPE.Orbits OPE.Nesting Trace.Pilot RG17 Spec
open private small span from YM.Integration.WilsonThermometerUnitFilingWindowRates
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "hat!" i:max => R.family.path.levels.clock.hatBeta i
local notation "σ" => R.family.S.scale

include simple in
theorem original {K:ℝ} (kp:0≤K) {admitted:ℕ→Prop} (enrolled:∀ᶠ v:ℕ in atTop,admitted v):
    ∀ᶠ b:ℕ in atTop,∀v:ℕ,v≤b → σ b-σ v ≤ K*Real.log (4*(hat! b))+(1+Real.log (hat! b)) →
    admitted v ∧ ∀N per:ℕ,b<N → (0<regulatorRun C N per (v+1) ∧
      regulatorRun C N per (v+1) ≤ 4*regulatorRun C N per (b+1)):=by
  obtain ⟨j₀,next⟩:=eventually_atTop.1 (RG01.Physical.nextHat simple R.alloy.B.a)
  obtain ⟨a,started⟩:=eventually_atTop.1 enrolled
  have slope:=Gauge.slopeConstant_pos simple
  have kd:0≤G.slopeConstant*(5*K+2):=by positivity
  have rate:=Next.Rank.Station.hat_rate (C).path.levels simple
  filter_upwards [rate (small kd),rate (eventually_ge_atTop (2*(hat! a)+1)),eventually_ge_atTop j₀] with b enough tall late
  change G.slopeConstant*(5*K+2)*(1+Real.log (hat! b)) ≤ (hat! b)/2 at enough
  change 2*(hat! a)+1 ≤ hat! b at tall
  intro v vb window
  have jp:1≤hat! b:=((C).path.levels.fits.delayed b).le
  have sub:=window.trans (span kp jp)
  have affine:(hat! b)-(hat! v)=G.slopeConstant*(σ b-σ v):=by dsimp [Calendar.hatBeta];ring
  have prior:(hat! b)/2 ≤ hat! v:=by
    have scaled:=mul_le_mul_of_nonneg_left sub slope.le
    rw [←affine] at scaled
    nlinarith only [scaled,enough]
  have mono:=WilsonThermometerUnitFilingWindowRates.increasing R simple
  refine ⟨started v (by by_contra! small;have alt:=mono small.le;linarith only [tall,prior,alt]),?_⟩
  intro N per above
  let beta:=fun i=>((C).path.rep N per i).beta
  have bv:= (R.makes.wilson.represents N per (v+1) (by omega)).band
  have bb:= (R.makes.wilson.represents N per (b+1) above).band
  have low:(hat! (v+1))/2≤beta (v+1):=bv.1
  have high:beta (b+1)≤2*(hat! (b+1)):=bb.2
  have add:(hat! (b+1))≤2*(hat! b):=next b late
  have ep:0<beta (v+1):=(half_pos (zero_lt_one.trans ((C).path.levels.fits.delayed (v+1)))).trans_le low
  have bp:0<beta (b+1):=(half_pos (zero_lt_one.trans ((C).path.levels.fits.delayed (b+1)))).trans_le bb.1
  have precise:beta (b+1)≤16*beta (v+1):=by linarith only [add,prior,high,low,mono (Nat.le_succ v)]
  have bound:=Real.sqrt_le_sqrt precise
  rw [Real.sqrt_mul (by norm_num:0≤(16:ℝ)),show Real.sqrt (16:ℝ)=4 by norm_num] at bound
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr ep),?_⟩
  change (Real.sqrt (beta (v+1)))⁻¹≤4*(Real.sqrt (beta (b+1)))⁻¹
  rw [←div_eq_mul_inv,(le_div_iff₀ (Real.sqrt_pos.mpr bp))]
  rwa [inv_mul_eq_div,(div_le_iff₀ (Real.sqrt_pos.mpr ep))]

end YM.Integration.WilsonThermometerUnitFilingFlatArrival
