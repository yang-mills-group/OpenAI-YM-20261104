import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNestedFieldColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedRealFiledCoupling
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPhysicalConversionEntry

noncomputable section
namespace IssuedBridge.PostedAppointedFieldCorrelation
open YangMills YangMills.Wilson
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {R : Run g.core}
variable {simple : g.core.Simple} (Z : WilsonPrescription g.core)
open MS MS.Land MS.Fleet FVA2.Scale WilsonViewerReportingGrid WilsonThermometerWeakMeasuredSeries
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open PostedMeasuredCompactCorrelation (leaves)
variable (raw : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
variable {σ : Prescription (Press.portDeck g.core)} {dial : Bool} (matched : Main.Match Z simple raw σ dial)

open YM.FVA2.Scale YM.MS YM.MS.Fleet YM.MS.Land YangMills.Matching
include matched in
theorem original (μ : ℝ) {n h : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (within : ∀ i, d i ≤ h) (x : Stage n) (k : ℕ) :
    Jury.fxt (Measure.outlook Z.scheme Z.criterion h) x.val k
        (commonCaps (PostedMeasuredCompactCorrelation.leaves (R:=R) d v) within) =
      ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
        if (∑ i, (ν i).val) ≤ k then
          (couplingPower (PostedRealFiledCoupling.coefficient Z raw μ) j.val (k-∑ i, (ν i).val) : ℂ) *
          Equator.wave μ raw h n x j.val (fun i => XSpace.Normalize.up (within i)
            ((PowerSeries.coeff (ν i).val (Measure.Z Z.scheme Z.criterion μ raw (d i))) (v i))) else 0 := by
  classical
  rw [Jury.fxt, dif_pos x.property]
  rw [PostedPhysicalConversionEntry.original Z raw matched μ _
    (PostedRealFiledCoupling.original Z raw matched μ).1]
  simp_rw [PostedNestedFieldColumns.original (R:=R) Z raw matched μ d v within]
end IssuedBridge.PostedAppointedFieldCorrelation
end
