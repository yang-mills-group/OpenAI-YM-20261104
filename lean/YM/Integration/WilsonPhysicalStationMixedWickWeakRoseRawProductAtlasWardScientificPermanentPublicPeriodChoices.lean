import YM.Integration.WilsonPhysicalStationMixedWickCommissionRun
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPhaseData

noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodChoices
open WilsonOriginalGeneralRosterOriginalCourse
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

open Climb Lattice Filter Function Set Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open RG RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedMixedMasterSchool (field)
open WilsonOriginalGeneralRosterUnion (Row)
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open XSpace
open WilsonOriginalOpticalSchedule (prepared)
open scoped Classical Topology
variable {G:Gauge}

theorem original (axis:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(σ:WilsonOriginalAllOrderCourse.Schedule G):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
    RestoredBooking WilsonIndependentRestoredPublicRates.tolerance R.b ∧ WilsonMovingForkReporterBasisOnRun.Banks R ∧ ∃p:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared σ) R T W,
    ∃lamp:WilsonReportLampForecast.Ready R.family.path.levels,∃paths:FundedOriginalVacuumPaths.prices R.kit,
    Lower p paths lamp ∧
    ∀(cohort:Ultrafilter (ℕ×ℕ)→Prop),(∀(v:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤v.fuse→cohort l)→
      ∀(request:ℕ→ℕ)(hp:StrictMono request), let v:Extraction.Order:=⟨.full,⟨request,hp⟩⟩
      ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (L:EveryPhase.Almanac F)(Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(H:(Bel R.family.book).Hierarchy),
      ∃z:Trace.Terrace.Arch R.family,∃l:Ultrafilter (ℕ×ℕ),∃J:ℝ→PhysMS.tower S,
      ∃chosen:WilsonViewerElectedHierarchy.Selected.{u} F L Q J H z l simple cohort,
        Household p chosen.bliss chosen.leading chosen.obeys chosen.original lamp ∧
        Nonempty (WilsonPhysicalAllGradeWeakElection.Assignment F J H l simple) ∧
        WilsonPhysicalStationMixedWickPose.Finance (Y:=l) (Z:=z) simple F H ∧
        (∀Jc:ℝ→PhysMS.tower S,∀posed:WilsonViewerElectedHierarchy.Selected.{u} F L Q Jc H z l simple cohort,
          Household p posed.bliss posed.leading posed.obeys posed.original lamp) ∧
        WilsonPhysicalStationMixedWickCommissionRun.Reported.{u} R F (l:=l) J H (arch:=z) L Q cohort simple p ∧
        StrictMono w.per.choose ∧ (v.refine w).per.choose=request ∘ w.per.choose ∧
        WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPhaseData.Recovered chosen :=by
  classical
  obtain ⟨R,T,W,restored,banks,p,lamp,paths,lower,orders⟩:=
    WilsonOriginalGeneralRosterOriginalCourse.measured_cap_station_ports.{u} axis simple positive σ
  refine ⟨R,T,W,restored,banks,p,lamp,paths,lower,?_⟩
  intro cohort eligible request hp v
  obtain ⟨w,S,F,L,Q,H,arch,l,J,chosen,old,assignment,finance,apartments,source⟩:=orders cohort eligible v
  exact ⟨w,S,F,L,Q,H,arch,l,J,chosen,old,assignment,finance,apartments,source,w.per.monotone,rfl,
    WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPhaseData.original chosen⟩

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodChoices
end
