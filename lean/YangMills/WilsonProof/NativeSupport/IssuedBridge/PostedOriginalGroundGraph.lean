import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNestedFieldColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedRealFiledCoupling
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPhysicalConversionEntry

noncomputable section
namespace IssuedBridge.PostedOriginalGroundGraph
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
theorem original (μ : ℝ)
    {n h : ℕ} (d : Fin n → ℕ) (within : ∀ i, d i ≤ h)
    (b : (i : Fin n) → (maxwellReference g).sector (d i)) (x : Stage n) :
    Equator.wave μ raw h n x 0 (fun i => XSpace.Normalize.up (within i) (b i)) =
      (maxwellReference g).moment x.val (fun i => (b i).val) := by
  rw [Equator.before μ raw n x]
  rfl

end IssuedBridge.PostedOriginalGroundGraph
end
