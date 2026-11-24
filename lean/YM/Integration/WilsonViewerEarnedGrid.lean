import YM.Integration.WilsonViewerAlignedPublic
import YM.Integration.WilsonViewerPhysicalRelease

set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato Lattice
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonThermometerWeakMeasuredSeries WilsonPositionHomogeneousFrame
open WilsonViewerGridPins WilsonViewerReportingGrid WilsonViewerAlignedResidual
open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {L:EveryPhase.Almanac F} {Y:(Bel R.family.book).Hierarchy}
    {arch:Trace.Terrace.Arch R.family} {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop} (run:Selected.{u} F L Q J Y arch ℓ simple cohort)


variable (Z:WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    {branch : Bool} (ms : Main.Match Z simple M σ branch)
    (rose : ℝ → Group R.family 6) (book : Book (f:=f) (l:=ℓ) (H:=Y) rose J)
    {B : ℕ} (hB : 0<B) (pace : WilsonWindowReportingPace.Slow R.kit) (fine index : ℝ → ℕ)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index
local notation "issued" => WilsonMaxwellThermometerKineticRequest.earned (Y:=ℓ) Z F J rose simple (B:=B) fine index

include run book hB pace in
/-- The measured Rose fixes the actual physical coupling before choosing one reporting
grid for every position, order, derivative and viewer in a fixed finite horizon. -/
theorem Selected.earned_grid (schedule:enrolled) (ν:ℝ){m:ℕ}(d₀:ℕ)(φ:Test m)
    (v₀:Fin m→Sec G d₀)(first:issued d₀ φ v₀ 1) :
    Coupling G θ ∧ ∀ H,∃ P:Report F ℓ H θ,∀(n:ℕ)(d:Caps n)(v:MaxwellSlots R.family d)
    (within:∀i,d i≤H)(W:Finset E4)(j p q:ℕ),WilsonThermometerWeakSignedJets.high j p≤q →
    PinBill Z M ms ν v within P W (WilsonThermometerWeakSignedJets.high j p+1) q →
    ∀ K, IsCompact K → K⊆conf n → ∀ ε:ℝ,0<ε → ∀ᶠr in trail,∀x∈K,∀viewer:Viewers F,
      ‖iteratedFDeriv ℝ j (measured F viewer (homogeneous F J Z r) v r) x-
        iteratedFDeriv ℝ j (approximate (coefficient Z M ν H (commonCaps v within)) p (θ r)) x‖≤ε*(θ r)^p := by
  have real:Coupling G θ := (WilsonMaxwellThermometerKineticRelease.running Z F J rose simple hB pace
    fine index run.bliss book run.leading schedule d₀ φ v₀ first).2.2
  refine ⟨real,?_⟩
  intro H
  obtain ⟨P⟩:=run.report H θ real
  exact ⟨P,fun n d v within W j p q retain paid=>
    run.aligned_positions Z M ms ν v within P W j p q retain real paid⟩

end YM.Integration.WilsonViewerElectedHierarchy
end
