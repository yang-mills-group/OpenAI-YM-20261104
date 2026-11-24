import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedConversionFields
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedRawSlope
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFreeTriangle
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedTriangleIntegrability
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedClockReading
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedScalarReversion
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFiledFrameCorrection
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedScreenBalance
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
noncomputable section
namespace IssuedBridge.PostedAppointedConversionValid
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
local notation "B" => _root_.IssuedMaxwell.Reports.B g
local notation "W" => PostedPositionConversion.filed Z raw matched




open MeasureTheory


local notation "GC" => _root_.IssuedMaxwell.GraphCoefficients.issued g
local notation "M₀" => WilsonCapturedPhysicalMSDatum.original g.core
local notation "μ₀" => Teller.logNu 1
open PostedScreenedReparametrization (screened)


variable (h : g.IsSimple)
local notation "P₀" => Subtype.val (_root_.IssuedMaxwell.ElectedPrescription.prior g h)
local notation "H₀" => Subtype.property (_root_.IssuedMaxwell.ElectedPrescription.prior g h)
local notation "Z₀" => _root_.IssuedMaxwell.ElectedPrescription.issued g h

open YangMills.MSbar.Position (rawFrame framePrefix)
theorem original (lamp : Bool) : YangMills.MSbar.ConversionValid GC P₀ (PostedAppointedConversionFields.filed h lamp) := by
  obtain ⟨coupling, fields, inverseFields, correction, factorization⟩ :=
    PostedAppointedConversionFields.original h lamp
  refine
    { raw := PostedAppointedRawFrame.original h
      integrable := PostedAppointedTriangleIntegrability.original h
      freeOffset := PostedAppointedFreeTriangle.original h
      rawSlope := PostedAppointedRawSlope.original h
      signedTree := PostedAppointedClockReading.tree h
      nonzeroTree := PostedAppointedClockScale.nonzero h
      real := (PostedAppointedClockReading.signed h).1
      slope := (PostedAppointedClockReading.signed h).2
      coupling := coupling
      inverseReading := ?_
      fields := fields
      inverseFields := inverseFields
      correction := correction
      factorization := factorization
      startsAtIdentity := PostedPositionConversion.startsAtIdentity Z₀ M₀ (PostedAppointedConversionFields.elected h lamp) μ₀
      strictlyLowering := PostedPositionConversion.strictlyLowering Z₀ M₀ (PostedAppointedConversionFields.elected h lamp) μ₀ }
  rw [coupling]
  exact YangMills.MSbar.Position.reversion GC P₀ (PostedAppointedClockReading.signed h).2

def realized (lamp : Bool) : YangMills.MSbar.NumericalAdjustment B ((PostedAppointedConversionFields.filed h lamp)).adjustment :=
  PostedPositionConversion.realization Z₀ M₀ (PostedAppointedConversionFields.elected h lamp) μ₀

end IssuedBridge.PostedAppointedConversionValid
end
