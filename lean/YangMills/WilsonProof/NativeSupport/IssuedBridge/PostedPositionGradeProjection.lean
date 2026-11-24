import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedHomogeneousFieldColumns
import YangMills.WilsonProof.NativeSupport.MSGradeProjection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.PostedPositionGradeProjection
open YangMills YangMills.Wilson
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical
open MS MS.Land MS.Fleet FVA2.Scale WilsonViewerReportingGrid WilsonThermometerWeakMeasuredSeries
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open PostedMeasuredCompactCorrelation (leaves)
open YM.Maxwell.Wick
variable {g : YangMills.GaugeGroup} {d : ℕ}
theorem project (i : Fin (d+1)) : Matching.Grade.project (maxwellReference g) d i.val = Level.proj (G:=g.core) i := by
  apply LinearMap.ext
  intro v
  exact Subtype.ext rfl
theorem original (A : Module.End ℂ ((maxwellReference g).sector d)) :
    Matching.Grade.diagonal (maxwellReference g) d A=Level.diag A := by
  unfold Matching.Grade.diagonal Level.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [project]
  rfl
theorem filed (Z : WilsonPrescription g.core) (raw : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
    {σ : Prescription (Press.portDeck g.core)} {dial : Bool} {simple : g.core.Simple}
    (matched : Main.Match Z simple raw σ dial) (μ : ℝ) (d k : ℕ) :
    Matching.Grade.diagonal (maxwellReference g) d (PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d)) =
    PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d) :=
  (original _).trans ((matched.frame μ d).2 k)
end IssuedBridge.PostedPositionGradeProjection
