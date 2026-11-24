import MSConversion
import YangMills.WilsonProof.NativeSupport.MSFormalSeries
import MSPositionFrame
import MSPositionPrescription
import MSPositionScreens
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.MSPositionLabels
import MSScalarReverse
import MSScalarInverse
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFieldBank
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAxisFieldColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedHomogeneousFieldColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedRealFieldColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedOriginalFieldInverse
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedRealFiledCoupling
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedConversion
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAdjustmentColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNumericalPositionFrame
noncomputable section
namespace IssuedBridge.PostedPositionConversion
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

def filed (μ : ℝ) : YangMills.MSbar.PositionConversion (maxwellReference g) where
  conversion := PostedAppointedConversion.filed Z raw matched μ
  adjustment := fun d k => PowerSeries.coeff k (Measure.adjust Z.scheme Z.criterion d)

def realization (μ : ℝ) : YangMills.MSbar.NumericalAdjustment (maxwellReference g)
    (filed Z raw matched μ).adjustment :=
  PostedNumericalAdjustment.filed Z (WilsonPositionHomogeneousCoefficients.purchased Z matched)

theorem original (μ : ℝ) : (filed Z raw matched μ).conversion.Zinv =
    YangMills.MSbar.Series.inverseFrame (maxwellReference g) (filed Z raw matched μ).conversion.Z := by
  funext d k
  let A := Measure.Z Z.scheme Z.criterion μ raw d
  have eq : PowerSeries.mk (fun j => PowerSeries.coeff j A) = A := by
    apply PowerSeries.ext
    intro j
    exact PowerSeries.coeff_mk j (fun i => PowerSeries.coeff i A)
  change PowerSeries.coeff k (PowerSeries.invOfUnit A 1) =
    PowerSeries.coeff k (PowerSeries.invOfUnit (PowerSeries.mk (fun j => PowerSeries.coeff j A)) 1)
  rw [eq]

theorem startsAtIdentity (μ : ℝ) (d : ℕ) : (filed Z raw matched μ).adjustment d 0 = LinearMap.id :=
  PostedAdjustmentColumns.atZero Z (WilsonPositionHomogeneousCoefficients.purchased Z matched) d

theorem strictlyLowering (μ : ℝ) (d h k : ℕ) (p : (maxwellReference g).sector d)
    (hp : YangMills.Matching.Homogeneous (maxwellReference g) h p.val) :
    ∀ m ∈ ((filed Z raw matched μ).adjustment d (k+1) p).val.support,
      Finsupp.weight (fun i : (maxwellReference g).toCoordinates.Key => i.1 + 2) m < h :=
  PostedAdjustmentColumns.original Z (WilsonPositionHomogeneousCoefficients.purchased Z matched) d h k p hp
end IssuedBridge.PostedPositionConversion
end
