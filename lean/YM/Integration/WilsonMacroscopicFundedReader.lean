import YM.Integration.WilsonMatrixTicketLanesStrongSeed
import YM.Integration.WilsonMatrixTicketLanesRetained
import YM.Integration.WilsonMatrixTicketLanes
import YM.Integration.WilsonMatrixTicketLanesChargeSource
import YM.Integration.WilsonMacroscopicSharpPacket

/-! Elect the matrix-priced physical table before fixing the marked position
    hierarchy. The marked cohort is released on its actual ordered subfilter. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMacroscopicFundedReader
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)

/-- All orders use a single reader, limit law, charged program and field hierarchy
    for each original extraction order. -/
def Elected (cohort:Ultrafilter (ℕ×ℕ)→Prop):Prop:=
  ∀v:Extraction.Order,∃(w:Extraction.Order)(S:Table R.family.book)
    (F:Final R.family (v.refine w) S)(L:EveryPhase.Almanac F)
    (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin),
    EveryPhase.Completed F L ∧ Trace.Target.Result.{u} F simple ∧ Trace.Target.Exclusion.{u} F ∧
    Facilities R.family (v.refine w) S ∧ Orbits.Foundation F Q ∧ SingleLog F Q.port ∧
    ∃(Y:(Bel R.family.book).Hierarchy)(Z:Trace.Terrace.Arch R.family)(l:Ultrafilter (ℕ×ℕ))
      (_bliss:Bliss F l Z Y)(P P':ℝ→Spin.change S 4)(J:ℝ→PhysMS.tower S)
      (φ:E4→ℝ)(a d e:ℝ→ℝ), (∀ᶠr in trail,J r 4=P' r) ∧
      Trace.Target.XScheme F simple Y l P P' φ ∧ Trace.Target.FieldComparison F Y Z P P' a d e ∧
      Leading F J ∧ (∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d) ∧
      (l:Filter (ℕ×ℕ)) ≤ (v.refine w).fuse ∧ cohort l ∧
      Log.MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter (ℕ×ℕ))

theorem original {T:Campaign R} (W:Campaign.Pillars R T) {κ:ℝ}
    (fund:FundedOriginalProperties.{u} simple κ W)
    (physical:WilsonMatrixTicketFuelPrice.FromStrongBin R.family)
    (cohort:Ultrafilter (ℕ×ℕ)→Prop)
    (issued:∀(f:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤f.fuse→cohort l):
    Elected.{u} R simple cohort:=by
  intro v
  obtain ⟨w,A,rows,B,z,tr,S,E,projected,base,⟨seed⟩,strong,_⟩:=
    WilsonMatrixTicketLanesStrongSeed.original R simple v
  obtain ⟨F,X,L,Q,_,_,done,trace,omitLaw,fac,foundation,_,_,_⟩:=
    WilsonMatrixTicketLanesRetained.original simple W fund (v.refine w) base seed
  have lanes:=physical (v.refine w) A rows B z tr S E F projected base strong fac.toServices
  obtain ⟨Y,Z,l,bliss,P,P',J,φ,a,d,e,grade,scheme,comp,lead,obedient⟩:=
    Frame.meter_found.{u} simple F trace
  have bill:=WilsonMatrixTicketLanes.on_ultrafilter lanes l bliss.lies
  exact ⟨w,S,F,L,Q,done,trace,omitLaw,fac,foundation,first_log F fac bliss.lies bill Q.spans,
    Y,Z,l,bliss,P,P',J,φ,a,d,e,grade,scheme,comp,lead,obedient,bliss.lies,issued _ _ bliss.lies,bill⟩

end YM.Integration.WilsonMacroscopicFundedReader

