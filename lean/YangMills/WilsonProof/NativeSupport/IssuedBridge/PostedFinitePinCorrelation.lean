import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedObservedCompactExpansion
import YM.Integration.WilsonFinitePinValued
import YM.FVA2.DerivD.Picture
import YM.Integration.WilsonCapturedPhysicalMSDatum
import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces
import YM.Integration.WilsonOriginalGeneralRosterFirstJoin
import YM.Integration.WilsonOriginalPublicTrialPhaseUncutField
import YM.Integration.WilsonPhysicalBookedConclusions
import YM.Integration.WilsonPhysicalStationMixedWickCommission
import YM.Integration.WilsonPositionSeparatedProfileUnitFrame
import YM.Integration.WilsonPositivePursePosition
import YM.Integration.WilsonReceivedChronologicalRosterJointPeriod
import YM.Integration.WilsonReceivedChronologicalRosterOuterHomeMesh
import YM.Integration.WilsonReceivedChronologicalRosterPhysicalFaces
import YM.XSpace.Pivots

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace IssuedBridge.PostedFinitePinCorrelation
open YM YM.Integration
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato Lattice
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonThermometerWeakMeasuredSeries WilsonPositionHomogeneousFrame
open WilsonViewerGridPins WilsonViewerReportingGrid WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {L:EveryPhase.Almanac F} {Y:(Bel R.family.book).Hierarchy}
    {arch:Trace.Terrace.Arch R.family} {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop} (run:Selected.{u} F L Q J Y arch ℓ simple cohort)

variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{dial:Bool}(matched:Main.Match Z simple M σ dial)(ν:ℝ)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => WilsonPositionHomogeneousFrame.homogeneous F J Z


open MeasureTheory
variable {n H : ℕ} (d : Caps n) (within : ∀ i, d i ≤ H)
include run matched in
theorem original (thermal : Coupling G θ) (P : Report F ℓ H θ) (v : MaxwellSlots R.family d)
    (price : ∀ p : ℕ, ∃ (W : Finset E4) (q : ℕ), WilsonThermometerWeakSignedJets.high 0 p ≤ q ∧
      WilsonPositionScaleLawPowerPinLimit.Price Z M ν v within P W (WilsonThermometerWeakSignedJets.high 0 p+1) q)
    (who : Viewers F) :
    YangMills.Matching.HasExpansion 0 θ (fun r => measured F who (pub r) v r)
      (fun k x => Jury.fxt (Measure.outlook Z.scheme Z.criterion H) x k (commonCaps v within)) := by
  apply PostedObservedCompactExpansion.original
  · intro k
    exact WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveIntegral.opening Z M matched ν k _
  · have born : ∀ᶠ r : ℝ in trail, 0 < r := self_mem_nhdsWithin
    exact born.mono (fun r hr => WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveIntegral.physical
      F (pub r) v hr who)
  · intro K compact sep p ε eps
    obtain ⟨W,q,depth,bought⟩ := price p
    have invoice := (WilsonPositionScaleLawPowerPinLimit.original (R:=R) (F:=F) (J:=J)
      Z M matched ν v within P W (WilsonThermometerWeakSignedJets.high 0 p+1) q thermal.positive).mpr bought
    have paid := run.aligned_positions Z M matched ν v within P W 0 p q depth thermal invoice K compact sep ε eps
    filter_upwards [paid,thermal.positive] with r cost heat x hx
    have value := cost x hx who
    simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,← map_sub,LinearIsometryEquiv.norm_map] at value
    rw [← WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveCharged.valued Z M matched ν p (θ r) _ (sep hx),
      WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveIntegral.form,← Fin.sum_univ_eq_sum_range] at value
    simpa only [abs_of_pos heat] using value
end IssuedBridge.PostedFinitePinCorrelation
end
