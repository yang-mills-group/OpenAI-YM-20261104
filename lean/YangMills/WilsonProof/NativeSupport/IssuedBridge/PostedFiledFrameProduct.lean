import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPositionConversion
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
namespace IssuedBridge.PostedFiledFrameProduct
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

def nativeFrame (μ : ℝ) : Series.Frame B := fun d k =>
  PowerSeries.coeff k (Measure.liftT Z.criterion μ raw d)

theorem original (μ : ℝ) :
    Series.cauchy B (nativeFrame Z raw μ) (W μ).adjustment = (W μ).conversion.Z := by
  funext d k
  let A := Measure.liftT Z.criterion μ raw d
  let C := Measure.adjust Z.scheme Z.criterion d
  let term := fun i : ℕ => PowerSeries.coeff i A * PowerSeries.coeff (k - i) C
  change (∑ i : Fin (k+1), term i.val) = PowerSeries.coeff k (A * C)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Fin.sum_univ_eq_sum_range]
end IssuedBridge.PostedFiledFrameProduct
end
