import YM.Integration.WilsonPhysicalAllGradeWeakElection
import YM.Integration.WilsonPhysicalStationMixedWickPose

/-! Keep the original grade-four comparison for every admitted physical chart. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalStationMixedWickFinance
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Classical Topology

open WilsonPhysicalAllGradeWeakElection (Assignment)
variable {G:Gauge}(R:Run G)(simple:G.Simple)(cohort:Ultrafilter (ℕ×ℕ)→Prop)
theorem original {T:Campaign R}(W:Campaign.Pillars R T){κ:ℝ}
    (fund:FundedOriginalProperties.{u} simple κ W)(physical:WilsonMatrixTicketFuelPrice.FromStrongBin R.family)
    (issued:∀(f:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤f.fuse→cohort l)
    (v:Extraction.Order):
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (L:EveryPhase.Almanac F)(Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (J:ℝ→PhysMS.tower S)(Y:(Bel R.family.book).Hierarchy)(arch:Trace.Terrace.Arch R.family)
      (l:Ultrafilter (ℕ×ℕ)),WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y arch l simple cohort ∧
      Nonempty (Assignment F J Y l simple) ∧ WilsonPhysicalStationMixedWickPose.Finance (Y:=l) (Z:=arch) simple F Y:=by
  obtain ⟨w,A,rows,B,z,tr,S,E,projected,base,⟨seed⟩,strong,_⟩:=
    WilsonMatrixTicketLanesStrongSeed.original R simple v
  obtain ⟨F,X,L,Q,_,_,done,trace,omitLaw,fac,foundation,_,_,_⟩:=
    WilsonMatrixTicketLanesRetained.original simple W fund (v.refine w) base seed
  have lanes:=physical (v.refine w) A rows B z tr S E F projected base strong fac.toServices
  obtain ⟨Y,arch,l,bliss,-,finance⟩:=trace.stress
  obtain ⟨day,rise,sold⟩:=WilsonPhysicalWeakRisingStaff.original simple F Y bliss
  obtain ⟨_,J,P',φ,a,d,e,same,scheme,comp,change,leading,obeys⟩:=
    WilsonPhysicalWeakSundial.original simple F Y bliss day rise sold finance
  have bill:=WilsonMatrixTicketLanes.on_ultrafilter lanes l bliss.lies
  exact ⟨w,S,F,L,Q,J,Y,arch,l,⟨done,trace,omitLaw,fac,foundation,first_log F fac bliss.lies bill Q.spans,
    bliss,bliss.lies,issued _ _ bliss.lies,bill,leading,obeys,
    ⟨fun r=>provisional day r 4,P',φ,a,d,e,same,scheme,comp⟩⟩,⟨⟨day,rise,sold,change⟩⟩,finance⟩

end YM.Integration.WilsonPhysicalStationMixedWickFinance
