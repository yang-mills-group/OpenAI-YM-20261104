import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedPinFrame

noncomputable section
namespace IssuedBridge.PostedNestedFieldColumns
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

theorem raised {n h : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (within : ∀ i, d i ≤ h) (i : Fin n) :
    commonCaps (leaves (R:=R) d v) within i = XSpace.Normalize.up (within i) (v i) := by
  simp [commonCaps, PostedMeasuredCompactCorrelation.leaves, YM.Maxwell.Free.scheme, XSpace.Normalize.up]

include matched in
theorem original (μ : ℝ) {n h : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (within : ∀ i, d i ≤ h) (i : Fin n) (j : ℕ) :
    (PowerSeries.coeff j (Measure.Z Z.scheme Z.criterion μ raw h))
        (commonCaps (leaves (R:=R) d v) within i) =
      XSpace.Normalize.up (within i)
        ((PowerSeries.coeff j (Measure.Z Z.scheme Z.criterion μ raw (d i))) (v i)) := by
  rw [raised]
  exact matched.frameCompat μ (d i) h (within i) j (v i)
end IssuedBridge.PostedNestedFieldColumns
end
