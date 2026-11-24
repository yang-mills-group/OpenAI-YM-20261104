import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFiledFrameProduct
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPositionGradeProjection
noncomputable section
namespace IssuedBridge.PostedFiledFrameDiagonal
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

open YangMills.MSbar
local notation "B" => maxwellReference g
local notation "W" => PostedPositionConversion.filed Z raw matched


open PostedFiledFrameProduct (nativeFrame)

theorem original (μ : ℝ) :
    (W μ).conversion.Z = Series.gradeFrame B (nativeFrame Z raw μ) := by
  let H := matched.details.toServed.toPosted.toQuoted.toContract.toMission.born
  funext d k
  have eq := Measure.equator Z.scheme Z.criterion μ raw σ simple H.Taylor H.still H.base (d := d)
  change PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d) =
    Matching.Grade.diagonal B d (PowerSeries.coeff k (Measure.liftT Z.criterion μ raw d))
  rw [PostedPositionGradeProjection.original, eq]
  exact PowerSeries.coeff_mk k _

theorem inverse (μ : ℝ) :
    (W μ).conversion.Zinv = Series.inverseFrame B (Series.gradeFrame B (nativeFrame Z raw μ)) := by
  rw [← original Z raw matched μ]
  exact PostedPositionConversion.original Z raw matched μ
end IssuedBridge.PostedFiledFrameDiagonal
end
