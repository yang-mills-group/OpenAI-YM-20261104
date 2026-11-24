import YM.Integration.WilsonCenteredFourCutoffRows
import YM.Integration.WilsonReportPrescribedFrame

/-! Funded physical basis reports on the very filter of the selected MatrixTicket.
The provisional optical frame at the original reporting date buys the prescribed
tower on the same Arch. The cutoff source and its Spindle fee use the true layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredSelectedLayout
open Function Filter Set MeasureTheory Lattice Wilson RG Extraction Extraction.Banks Table Spec
open OPE OPE.Orbits RG12 RG17 SharpGram Next.Rank PhysMS Trace.Pilot Trace.Terrace
open EveryPhase Climb PhysicalNext.Repeat.Legato WilsonViewerElectedHierarchy WilsonLimitConstruction
open scoped Classical Topology BigOperators
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→PhysMS.tower S)

theorem original {T:Campaign R}{W:Campaign.Pillars R T}{κ:ℝ}{simple:G.Simple}
    (fund:FundedOriginalProperties.{u} simple κ W)(pace:WilsonWindowReportingPace.Slow R.kit)
    {L:Almanac F}{Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {Y:(Bel R.family.book).Hierarchy}{arch:Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}(run:Selected.{u} F L Q J Y arch l simple cohort)
    (report:ℕ)(positive:0<report):
    let level:=WilsonMeasuredWindow.stop R.family.path.levels simple report
    let shift:=fun (d:ℕ) (_:ℝ)=>LinearEquiv.refl ℂ (R.family.label d)
    let layout:=WilsonOriginalBlissObserved.layout F run.bliss J level shift
    layout.lens=(l:Filter UVIndex) ∧
    (∀d,Pier.Lair.Paying F (Pier.Lair.tender F layout J) d) ∧
    ∀ d:ℕ,∃e:ℕ,∀ᶠr in trail,∀v:Free R.family d,∃y:R.family.label d,
      master layout d r y=J r d v ∧
      ∀N per:ℕ,level r≤N→Spindle.paid R.family d (level r) N per (atRef layout d r (N,per) y)
        ≤R.family.path.levels.clock.hatBeta (level r)^e*‖v‖:=by
  intro level shift layout
  obtain ⟨U⟩:=Lenses.attains_mantle17 F run.facilities.toServices l run.original fund.2.1.coverage
  let issued:ℝ→PhysMS.tower S:=fun r d=>Load.tent U (level r) d
  let window:=WilsonOriginalBlissObserved.layout F run.bliss issued level shift
  have pegs:Pegs U window:=⟨WilsonReportPhysicalFrame.reached simple pace positive,le_rfl,fun _ _=>rfl⟩
  have fees(d:ℕ):Pier.Lair.Paying F (Pier.Lair.tender F layout J) d:=
    Pier.Lair.prices F (WilsonReportPrescribedFrame.present F J run.leading run.obeys)
      d U run.facilities.toServices window pegs (WilsonReportPrescribedFrame.comparable simple pace positive)
  refine ⟨rfl,fees,fun d=>?_⟩
  obtain ⟨e,table⟩:=(fees d).affordability
  refine ⟨e,?_⟩
  filter_upwards [table,(WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple report positive).eventually_ge_atTop
    (R.family.ref d)] with r sale live
  intro v
  obtain ⟨y,bill,master⟩:=sale.1 v
  refine ⟨y,master,?_⟩
  intro N per in_date
  change Spindle.paid R.family d (layout.level r) N per (atRef layout d r (N,per) y)≤_
  rw [WilsonReportRegulatedSmear.reference layout r d y live in_date]
  exact bill

end YM.Integration.WilsonCenteredSelectedLayout
