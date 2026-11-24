import YM.Integration.WilsonReportingForestAngularFare
import YM.Integration.WilsonReportingForestCompactRoom

/-! The genuine one-step physical reflection estimate at a cutoff naming
exactly the actual submitted two-stage angular receipt, before all periods.
The incidence is at a fixed finite true cutoff N and at date j+1. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingForestAngularReflection
open Function Filter Set MeasureTheory Lattice Wilson RG Next.Rank Push.GridApprox
open PhysicalNext.Repeat.Legato Next.Scheduling Next.Scheduling.Clock OPE.Therm MSbar.Heath.Stock
open WilsonReportingForestAngularFare
open scoped ENNReal Topology BigOperators Classical
variable {G:Gauge}

/-- Unfolding the original StageThreshold (angularThreshold G) at the
original Realized family gives precisely these numerical entries. -/
def posted (R:Run G):Prop := ∀ j n,
  let A:=R.family.path.levels
  let P:=(A.clock.op j n).patch
  (eventually_atTop.mp (angular_fare G (A.params (j+1)) P.L P.J)).choose ≤ A.clock.hatBeta j

/-- Every translated actual plaquette, on the original normalized finite
Wilson marginal. The adjacent bare endpoint is allowed. -/
theorem original (R:Run G) (simple:G.Simple) (gate:posted R) (K:ℕ):
    ∀ᶠ j:ℕ in atTop, ∀ (N n:ℕ) (_:j+1≤N) (z:Face (Per (R.family.side (j+1) n))),
      let x:=R.family.path.levels.clock.hatBeta (j+1)
      (OPE.Therm.scene R.family.path N n (j+1)).real (trigger z (angularCut x)) ≤ (x⁻¹)^K := by
  let H:=R.family.path
  let A:=H.levels
  let C:=A.clock
  let sel:H.Selected:=R.T.choice
  have adv:=tendsto_add_atTop_nat 1
  filter_upwards [adjacent_room A,adv.eventually (Vac.treasury_stage A simple),
    adv.eventually ((log_raised (K:=A) simple).eventually_ge_atTop 1),
    adv.eventually (narrow (H:=H) simple), (A.fits.deep.comp adv).eventually_ge_atTop K] with j room price log1 below k0
  intro N n hj z x
  obtain ⟨a,z⟩:=z
  change (OPE.Therm.scene H N n (j+1)).real (trigger (a,z) (angularCut x)) ≤ _
  rw [displaced (H:=H) sel hj a z (angularCut x)]
  let P:=(C.op j n).patch
  let B:=A.params (j+1)
  let β:=(H.rep N n (j+1)).beta
  let g:=gap β
  have rep:=sel.represents N n (j+1) hj
  have hx:1<x:=A.fits.delayed _
  have b0:0<β:=by have f:=rep.band.1;change x/2≤β at f;linarith
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr b0)
  have band:g ≤ 2*cue x:=(band_gap x β (zero_lt_one.trans hx) (trial_in rep.band)).2
  have norm:β*g^2=1:=by unfold g gap;field_simp;exact (Real.sq_sqrt b0.le).symm
  have trial:g ≤ (H.rep N n (j+1)).p.threshold :=by
    rw [rep.vac];apply band.trans;apply le_trans _ below.2
    change 2*cue x ≤ 4*(cue x*(Real.log x)^12)
    have t0:1 ≤ Real.log x :=log1
    have g0:0<cue x:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hx))
    have h:=mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=12) t0) g0.le
    linarith only [h,g0]
  have raw:=away (p:=n) (τ:=angularCut x) sel (Nat.le_succ j) hj z room gp trial norm
  have geom:(H.S.toDepth (Nat.le_succ j) n).count.val=P.L.val:=by
    change (H.S.toDepth (Nat.le_succ j) n).count.val=(H.S.block j).val
    simp [YM.Schedule.toDepth,YM.Schedule.steps]
  have bought: (eventually_atTop.mp (angular_fare G B P.L P.J)).choose ≤ x :=
    (gate j n).trans (WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le (Nat.le_succ j))
  have earned :=(eventually_atTop.mp (angular_fare G B P.L P.J)).choose_spec x bought g gp band
  have kJ:K≤P.J:=k0
  refine raw.trans ((Real.exp_monotone ?_).trans (earned.trans ?_))
  · rw [geom];exact sub_le_sub_right (mul_le_mul_of_nonneg_left (add_le_add price le_rfl)
      (pow_nonneg (Nat.cast_nonneg _) 4)) _
  · exact pow_le_pow_of_le_one (inv_nonneg.mpr (zero_lt_one.trans hx).le) (inv_le_one_of_one_le₀ hx.le) kJ

end YM.Integration.WilsonReportingForestAngularReflection
