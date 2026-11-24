import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskIncome
import YM.Integration.WilsonPhysicalHistoryRetainedSpringTemperature
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskClock

/-! The price of the complete current masked incoming action is uniform in all
later cutoffs and torus periods at a fixed reporting order. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Comparison.RG02 Function Filter Lattice RG Wilson MeasureTheory OPE.Therm
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Ticket WilsonLimitConstruction Pert.Asymptotics
open private credits from YM.Integration.WilsonPhysicalHistoryRetainedSpringGrowth
open scoped Classical Topology
variable {G : Gauge}

private theorem stage_size (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (m:ℕ) :
    let V:=R.family.path.levels
    let j:=m+1
    let w:=1+V.clock.hatBeta j
    let D:=V.params j
    D.width⁻¹≤w ∧ D.paths≤w ∧ zz V j≤w := by
  intro V j w D
  have logpos:=Real.log_pos (V.fits.delayed j)
  have height : 0≤V.clock.hatBeta j:=zero_le_one.trans (V.fits.delayed j).le
  have extent : ActualRunAdmissionScales.profileCost V j≤V.clock.hatBeta j:=calc
    _≤((V.S.block m).val:ℝ):=ActualRunAdmissionScales.profileCost_le_block V m
    _≤Real.log (V.clock.hatBeta m):=WilsonFundedMeasuredWindow.paced R slow m
    _≤V.clock.hatBeta m:=Real.log_le_self (zero_le_one.trans (V.fits.delayed m).le)
    _≤_:=Push.Corrected.Last.band_le V simple (Nat.le_succ m)
  have h:=ActualRunAdmissionScales.profileCost_components V j
  have bound : V.clock.hatBeta j≤w:=by dsimp [w];linarith
  exact ⟨h.1.trans (extent.trans bound),h.2.1.trans (extent.trans bound),by
    change 1+Real.log (Real.log (V.clock.hatBeta j))≤1+V.clock.hatBeta j
    linarith only [(Real.log_le_self logpos.le).trans (Real.log_le_self height)]⟩

theorem cofinal_spring_mask_budget (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (heat : Poetry R.family.path.levels) (v:ℕ→Gear G→ℝ) (rows:FundedMarkedCoverRows.prices v R.kit)
    (credit:Credit) (d M r:ℕ) :
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,let j:=m+1
      let C:=credit.buy (zz V j)+zz V j*V.clock.loopCap j
      let B:=maskSpringConstant G d M*(1+V.clock.hatBeta j)^10
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*V.clock.forcedAllowance j
      ∀(N:ℕ),j<N→∀σ,0<σ→σ⁻¹≤zz V j→∀Z:SeriesA G,Draw Z σ C→Z.length≤M→
      (∀a∈Z,0<a.grade)→(∀a∈Z,a.grade≤d)→∀per (x:Site (R.family.side j per)),
        let g:=regulatorRun R.family N per j
        let f (U:Config G (R.family.side j per)):=maskedSpringAt R N per j r Z σ C g x U-springAt R N per j r Z g x U
        Measurable f ∧ (∀U,‖f U‖≤B) ∧ (∫U,‖f U‖ ∂scene R.family.path N per j)≤B*fee := by
  intro V
  obtain ⟨T,thermal⟩:=cofinal_temperature R simple v rows r
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (spring_mask_complete R simple heat 1),
    (tendsto_add_atTop_nat 1).eventually thermal,(tendsto_add_atTop_nat 1).eventually (credits V simple T credit)]
    with m bought state total
  intro j C B fee N later σ hs width Z draw count lower upper per x g f
  let D:=V.params j
  let p:=(R.family.path.rep N per j).p
  let w:=1+V.clock.hatBeta j
  have rep : R.family.path.Conv N per j:=R.makes.wilson.represents N per j later.le
  have one : 1≤w:=by dsimp [w];linarith [(V.fits.delayed j).le]
  have wx : V.clock.hatBeta j≤w:=by dsimp [w];linarith
  have wx3:=mul_le_mul_of_nonneg_left wx (by norm_num: (0:ℝ)≤3)
  have size:=stage_size R simple slow m
  have val:=state N later per
  have c:|g/Real.sqrt (finitePitch R N j r g)|≤2:=val.2.2.2.2.1.trans (by norm_num)
  have invoice:=bought N later.le per σ C hs Z draw d lower upper r g c x
  have dc:|D.clip.direct|≤1:=by
    rw [abs_of_pos D.clip.quadratic_pos]
    exact Push.PriceCompiler.Canonical.direct_le_one (R.alloy.B.support.cap j j le_rfl).metric
  have face : (((2*p.B+1)^4:ℕ):ℝ)≤625*w^8:=by
    dsimp only [p,w];rw [rep.vac];exact spring_cover_bound V j
  have grown:=mask_spring_growth G D.clip p one (val.2.1.trans (by norm_num))
    (val.1.trans (total.1.trans wx)) (val.2.2.2.2.2.trans wx3)
    dc D.paths_pos.le size.2.1 rep.good.paths.width size.1 hs (width.trans size.2.2) draw.1
    (total.2.trans wx3) face d Z.length M count
  have co:=cap_le_mask_rent G D.clip p rep.good.paths.width D.paths_pos.le hs draw.1 d Z.length
    (g^2*pitchTail R N j r g) (R.alloy.B.kin.alpha N j) (Integral.temperature g*finitePitch R N j r g)
  have fn: 0≤fee:=mul_nonneg (by positivity) (Real.exp_pos _).le
  refine ⟨invoice.1,fun U=>(invoice.2.1 U).trans (co.trans grown),le_trans ?_ (mul_le_mul_of_nonneg_right grown fn)⟩
  simpa only [pow_one] using invoice.2.2

end YM.Integration.OriginalMarkedRunAction
