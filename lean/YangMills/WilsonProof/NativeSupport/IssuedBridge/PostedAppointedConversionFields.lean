import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedRawFrame
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedClockReading
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedScalarReversion
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFiledFrameCorrection
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedScreenBalance
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
noncomputable section
namespace IssuedBridge.PostedAppointedConversionFields
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
def chosen (lamp : Bool) := ((_root_.IssuedMaxwell.ElectedPrescription.original g h).2.2.2.2 lamp).choose

theorem elected (lamp : Bool) : Main.Match Z₀ (_root_.IssuedMaxwell.ElectedPrescription.simple g h) M₀ (chosen h lamp) lamp := ((_root_.IssuedMaxwell.ElectedPrescription.original g h).2.2.2.2 lamp).choose_spec

def filed (lamp : Bool) := PostedPositionConversion.filed Z₀ M₀ (elected h lamp) μ₀

theorem inverse (k : ℕ) : PowerSeries.coeff k (Measure.f (Z₀).criterion μ₀ M₀) =
    ((YangMills.MSbar.Position.msCoupling GC P₀ k : ℝ) : ℂ) := by
  apply PostedScalarReversion.original
  · intro j
    exact (PostedAppointedClockReading.reading h j).symm.trans ((PostedAppointedClockReading.signed h).1 j).symm
  · exact YangMills.MSbar.Position.positionReading_zero GC P₀
  · exact (PostedAppointedClockReading.signed h).2

theorem coupling (lamp : Bool) : (filed h lamp).conversion.f = YangMills.MSbar.Position.msCoupling GC P₀ := by
  funext k
  exact congrArg Complex.re (inverse h k)

theorem frame (lamp : Bool) : PostedFiledFrameProduct.nativeFrame Z₀ M₀ μ₀ =
    YangMills.MSbar.Position.reparametrizedFrame GC P₀ := by
  rw [PostedScreenedReparametrization.original Z₀ M₀ (elected h lamp) μ₀, YangMills.MSbar.Position.reparametrizedFrame]
  have hf := coupling h lamp
  unfold filed at hf
  rw [hf]
  have eq : screened Z₀ M₀ μ₀ = YangMills.MSbar.Position.rawFrame GC P₀ := by
    funext d k
    exact PostedAppointedRawFrame.frameAgrees h d k
  rw [eq]
  rfl

theorem original (lamp : Bool) :
    (filed h lamp).conversion.f = YangMills.MSbar.Position.msCoupling GC P₀ ∧
    (filed h lamp).conversion.Z = Series.gradeFrame B (YangMills.MSbar.Position.reparametrizedFrame GC P₀) ∧
    (filed h lamp).conversion.Zinv = Series.inverseFrame B (Series.gradeFrame B (YangMills.MSbar.Position.reparametrizedFrame GC P₀)) ∧
    (filed h lamp).adjustment = Series.adjustment B (YangMills.MSbar.Position.reparametrizedFrame GC P₀) ∧
    Series.cauchy B (YangMills.MSbar.Position.reparametrizedFrame GC P₀) (filed h lamp).adjustment = (filed h lamp).conversion.Z := by
  erw [← frame h lamp]
  exact ⟨coupling h lamp, PostedFiledFrameDiagonal.original Z₀ M₀ (elected h lamp) μ₀,
    PostedFiledFrameDiagonal.inverse Z₀ M₀ (elected h lamp) μ₀, PostedFiledFrameCorrection.original Z₀ M₀ (elected h lamp) μ₀,
    PostedFiledFrameProduct.original Z₀ M₀ (elected h lamp) μ₀⟩
end IssuedBridge.PostedAppointedConversionFields
end
