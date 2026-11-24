import YM.Integration.WilsonPhysicalBookedConclusions
import YM.Integration.WilsonPhysicalWeakRegisteredGroup

/-! Before choosing any finite measurement, obtain the original phase, detector, and the actual transported
six-grade station on the already financed hierarchy. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalWeakPaidElection
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot Table
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakSundial WilsonPhysicalWeakSameStation
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}{a:Axis}{simple:G.Simple}
variable {κ:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
theorem original (cash:WilsonOriginalAllOrderCourse.Paid.{u} a simple κ s R T W)
    (cohort:Ultrafilter (ℕ×ℕ)→Prop)
    (admit:∀(f:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤f.fuse→cohort l)
    (v:Extraction.Order):
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (L:EveryPhase.Almanac F)(Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (J:ℝ→tower S)(Y:(Bel R.family.book).Hierarchy)(arch:Trace.Terrace.Arch R.family)
      (l:Ultrafilter (ℕ×ℕ))(run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y arch l simple cohort)
      (assignment:Assignment F J Y l simple)(A:ℝ→Group R.family 6),
      (∀r,∀cap:6≤(assignment.day r).1,A r=(trim cap (assignment.day r).2).room) ∧
      WilsonPositionCapTransport.Book (f:=v.refine w) (l:=l) (H:=Y) A (provisional assignment.day) ∧
      WilsonPositionCapTransport.Book (f:=v.refine w) (l:=l) (H:=Y) (through (provisional assignment.day) J A) J ∧
      type_of% (WilsonPhysicalCommonElection.before_limits run) := by
  obtain ⟨fund,_,_⟩:=WilsonPhysicalCommonElection.finances cash
  let lender:=OPE.Stroke.PoleC (OPE.Stroke.Earτ a simple)
  have lanes:=WilsonMatrixTicketFuelPrice.lanes R lender.price lender.charge cash.nested.1
  obtain ⟨w,S,F,L,Q,J,Y,arch,l,run,⟨assignment⟩⟩:=
    WilsonPhysicalAllGradeWeakElection.original R simple cohort W fund lanes admit v
  obtain ⟨A,source,raw,adjusted⟩:=WilsonPhysicalWeakRegisteredGroup.original F J simple assignment run.obeys 6
  exact ⟨w,S,F,L,Q,J,Y,arch,l,run,assignment,A,source,raw,adjusted,WilsonPhysicalCommonElection.before_limits run⟩

end YM.Integration.WilsonPhysicalWeakPaidElection
