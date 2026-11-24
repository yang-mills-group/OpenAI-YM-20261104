import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveIntegral
import YM.Integration.WilsonPositionScaleLawPowerPinLimit

/-! The finite sum identity on the same appointed mark and separated configuration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveCharged
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

variable {n H : ℕ}
open WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveIntegral (form)

include matched in
theorem valued (q:ℕ)(a:ℝ)(v:Fin n→Sec G H){y:Points n}(live:y∈conf n):
    form Z q a v y=approximate (coefficient Z M ν H v) q a y:=by
  unfold form WilsonThermometerWeakMeasuredSeries.approximate WilsonThermometerWeakCoefficientTail.part
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.real_smul,Complex.ofReal_pow]
  apply congrArg ((a:ℂ)^k * ·)
  change Jury.fxt (Measure.outlook Z.scheme Z.criterion H) y k v=
    WilsonPositionSeparatedProfileMatching.extended
      (fun x=>WilsonPositionHomogeneousComparison.coefficient Z M ν H x v k) y
  rw [WilsonPositionSeparatedProfileMatching.extended,dif_pos live,
    WilsonPositionHomogeneousComparison.filed Z M matched ν]
  exact congrArg (fun A=>A k v) (Jury.exactC _ (⟨y,live⟩:FVA2.Scale.Stage n))

end YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamFarArchiveCharged
end
