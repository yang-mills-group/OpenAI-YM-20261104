import YM.Integration.FVA1Physical.Wilson.AngularFare
import YM.Integration.FVA1Physical.Round2.StageThreshold

/-! A physical plaquette tail at a subthermal cutoff, before the period or the number of
subsequent integration steps is selected. The estimate is in the genuine normalized
Haar marginal of the history. -/
set_option autoImplicit false
set_option maxHeartbeats 760000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock Push.PriceCompiler Next.Foundations
open OPE.Therm MSbar.Heath.Stock Qlocal.Schedule
open scoped ENNReal Topology BigOperators Classical

def angularThreshold (G:Gauge) : StageThreshold := fun _ B P _ =>
  (eventually_atTop.mp (angular_fare G B P.L P.J)).choose

private theorem oneRoom {G:Gauge} (A:Levels G) : ∀ᶠ j:ℕ in atTop, room A j (j+1) 2 := by
  have pos:=Real.log_pos (one_lt_two (α:=ℝ))
  filter_upwards [((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (A.fits.deep.comp (tendsto_add_atTop_nat 1))).eventually_ge_atTop (370/Real.log 2)] with j due
  let p:=A.params (j+1)
  let L:ℝ:=(A.S.block j).val
  have large:1<L:=by have h:=A.S.block_large j;unfold L;exact_mod_cast (show 1<(A.S.block j).val from lt_of_lt_of_le (by decide) h)
  let K:=(A.clock.J (j+1):ℝ)
  have order:1≤K:=by have hz:=A.clock.adm (j+1);unfold K;exact_mod_cast (by omega : 1 ≤ A.clock.J (j+1))
  let x:=1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent
  have wide:2≤x:=by unfold x;linarith only [p.paths_pos,p.clip.radius_pos,p.columns_ge,p.price_pos,inv_pos.mpr p.width_pos]
  have bound:=(div_le_iff₀ (Real.log_pos large)).mp (show Real.log x / Real.log L ≤ (K^2)⁻¹ from A.fits.logCost j)
  rw [inv_mul_eq_div] at bound
  have growth:=(le_div_iff₀ (show 0<K^2 by positivity)).mp ((Real.log_le_log two_pos wide).trans bound)
  have slack:370*K≤L-1:=calc
    _ ≤ Real.log 2*K^2 := by change 370/Real.log 2 ≤ K at due;nlinarith only [mul_le_mul_of_nonneg_right ((div_le_iff₀ pos).mp due) (zero_le_one.trans order)]
    _ ≤ Real.log L:=growth
    _ ≤ L-1:= Real.log_le_sub_one_of_pos (zero_lt_one.trans large)
  let t:=A.S.a j
  have t0:0<t:=A.S.a_pos _
  have enough:2*((2:ℝ)+30*(K+5))<L:=by linarith only [slack,order]
  unfold Push.GridApprox.room Push.GridApprox.tail
  rw [A.S.a_step];push_cast
  change 2*(t/L*2+30*(t/L)*(K+5))<t
  field_simp;linarith [mul_lt_mul_of_pos_left enough t0]

variable {G:Gauge}

theorem angular_rare_on (R:PhysicalNext.Repeat.Legato.Run G) (simple:G.Simple)
    (gate:selectedThreshold (angularThreshold G) R.metals R.rolls R.alloy R.kit) (K:ℕ):
    ∀ᶠ j:ℕ in atTop, ∀ (N n:ℕ) (_:j+1≤N) (z:Face (Per (R.family.side (j+1) n))),
      let x:=R.family.path.levels.clock.hatBeta (j+1)
      (OPE.Therm.scene R.family.path N n (j+1)).real (trigger z (angularCut x)) ≤ (x⁻¹)^K := by
  let H:=R.family.path
  let A:=H.levels
  let C:=A.clock
  let sel:H.Selected:=R.T.choice
  have adv:=tendsto_add_atTop_nat 1
  filter_upwards [oneRoom A,adv.eventually (Vac.treasury_stage A simple),
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
end YM.Integration.FVA1Physical.Wilson
