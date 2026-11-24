import YM.Integration.WilsonCenteredFourMSParent
import YM.Integration.WilsonMacroscopicSharpPacket
import YM.Integration.WilsonViewerElectedHierarchy

/-! At each original extraction order the previously selected course, reader,
calibrated tower, matrix ticket and any marked cohort are fixed before either
vertex is specified. Both signed calorimeters act on that same course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourPhysicalSchool
open Filter Set Table Spec Extraction OPE OPE.Orbits OPE.Orbits.Reader EveryPhase PhysMS
open Trace Trace.Pilot Trace.Terrace RG17 XSpace XSpace.Normalize Maxwell MS MS.Land MS.Fleet MS.Theater
open Climb FVA2 FVA2.Register PhysicalNext.Repeat.Legato WilsonViewerElectedHierarchy WilsonLimitConstruction
open scoped Classical Topology
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)(simple:G.Simple)

def Filed : Prop:=
  (∀(n k h:ℕ)(d:Fin n→ℕ)(e:Fin k→ℕ)(v:Labels S d)(w:Labels S e)
    (M η δ:ℝ),0≤M→0<η→0<δ→WilsonMacroscopicSharpPacket.Sharp F Q h v w M η δ) ∧
  ∀(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)(branch:Bool),
    ∃σ:Prescription (Press.portDeck G),∃ms:Main.Match Z simple M σ branch,
    ∀(cap:ℕ)(fit:4≤cap)(other:S.Tag)(m:ℕ)(out:Q.channels m)(radius η:ℝ),0≤radius→0<η→
      WilsonCenteredFourMSParent.Hearing F J Z M ν ms Q fit other m out radius η

theorem selected {T:Campaign R}{W:Campaign.Pillars R T}{κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    {L:Almanac F}{Y:(Bel R.family.book).Hierarchy}{arch:Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}(run:Selected.{u} F L Q J Y arch l simple cohort):
    Filed F Q J simple:=by
  refine ⟨fun _ _ h _ _ v w _ _ _ m0 ep dp=>WilsonMacroscopicSharpPacket.on_ticket F Q run.facilities run.foundation
    run.original run.matrix h v w m0 ep dp,?_⟩
  intro Z M ν branch
  obtain ⟨σ,ms⟩:=Main.wilson_to_MS Z simple M branch
  exact ⟨σ,ms,fun _ included other m out _ _ r0 ηp=>WilsonCenteredFourMSParent.original F J Z M ν ms
    fund L run.phases run.leading run.obeys Q run.facilities run.original run.matrix run.bliss Z.store run.foundation
    included other m out r0 ηp⟩

theorem on_run {T:Campaign R}{W:Campaign.Pillars R T}{κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}(original:OnRun.{u} R simple cohort):
    ∀f:Extraction.Order,∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (f.refine w) S)
    (L:Almanac F)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(J:ℝ→PhysMS.tower S)
    (Y:(Bel R.family.book).Hierarchy)(arch:Arch R.family)(l:Ultrafilter (ℕ×ℕ)),
      Selected.{u} F L Q J Y arch l simple cohort ∧ Filed F Q J simple:=by
  intro v
  obtain ⟨w,S,F,L,Q,J,Y,A,l,receipt⟩:=original v
  exact ⟨w,S,F,L,Q,J,Y,A,l,receipt,selected F Q J simple fund receipt⟩

end YM.Integration.WilsonCenteredFourPhysicalSchool
