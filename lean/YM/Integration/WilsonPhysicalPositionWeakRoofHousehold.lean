import YM.Integration.WilsonOriginalGeneralRosterOriginalCourse
import YM.Integration.WilsonPhysicalPositionWeakRoofOnRun
import YM.Integration.WilsonIndependentRestoredPublicRates

/-! One original funded campaign issues both the paid upper roster
and the actual lower archive. The finite loss vector precedes every
thermal order. Every lower receipt uses that row's real test and the
complete union's reserve, cap, and pole. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterOriginalCourse

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

theorem restored (axis:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(σ:WilsonOriginalAllOrderCourse.Schedule G):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
    RestoredBooking WilsonIndependentRestoredPublicRates.tolerance R.b ∧ WilsonPhysicalPositionWeakRoofOnRun.Banks R ∧ ∃p:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared σ) R T W,
    ∃lamp:WilsonReportLampForecast.Ready R.family.path.levels,∃paths:FundedOriginalVacuumPaths.prices R.kit,
    Lower p paths lamp ∧
    ∀(cohort:Ultrafilter (ℕ×ℕ)→Prop),(∀(v:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤v.fuse→cohort l)→
      ∀v:Extraction.Order,∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (L:EveryPhase.Almanac F)(Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(H:(Bel R.family.book).Hierarchy),
      ∃z:Trace.Terrace.Arch R.family,∃l:Ultrafilter (ℕ×ℕ),∃J:ℝ→PhysMS.tower S,
      ∃chosen:WilsonViewerElectedHierarchy.Selected.{u} F L Q J H z l simple cohort,
        Household p chosen.bliss chosen.leading chosen.obeys chosen.original lamp:=by
  obtain ⟨R,T,W,⟨roofs,restored⟩,p,bank,lamp,paths⟩:=WilsonOriginalPhysicalFirstEntryOwnerFinance.roofed.{u}
    WilsonIndependentRestoredPublicRates.tolerance WilsonIndependentRestoredPublicRates.positive axis simple positive (prepared σ)
  refine ⟨R,T,W,restored,WilsonPhysicalPositionWeakRoofOnRun.original R simple roofs,p,lamp,paths,?_,?_⟩
  · intro I B U _ _ _ D term h d M E main pair precision outside w wanted
    exact WilsonOriginalGeneralRosterLowerInvoice.original (U:=U) p paths lamp term h d M E main pair precision outside w wanted
  intro cohort eligible v
  obtain ⟨w,S,F,L,Q,H,z,l,J,chosen,physical⟩:=WilsonOriginalGeneralRosterHomePhysical.onRun p bank lamp cohort eligible v
  exact ⟨w,S,F,L,Q,H,z,l,J,chosen,onFrame p chosen.bliss chosen.leading chosen.obeys chosen.original lamp
    (WilsonOriginalGeneralRosterHomeRegistered.onFrame p chosen.bliss chosen.leading chosen.obeys chosen.original physical)⟩

end YM.Integration.WilsonOriginalGeneralRosterOriginalCourse
end
