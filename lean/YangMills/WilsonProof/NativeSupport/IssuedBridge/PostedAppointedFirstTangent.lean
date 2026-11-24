import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFirstResponse
noncomputable section
namespace IssuedBridge.PostedAppointedFirstTangent
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




open MeasureTheory


local notation "GC" => _root_.IssuedMaxwell.GraphCoefficients.issued g
local notation "M₀" => WilsonCapturedPhysicalMSDatum.original g.core
local notation "μ₀" => Teller.logNu 1
open PostedScreenedReparametrization (screened)


variable (h : g.IsSimple)
local notation "P₀" => Subtype.val (_root_.IssuedMaxwell.ElectedPrescription.prior g h)
local notation "H₀" => Subtype.property (_root_.IssuedMaxwell.ElectedPrescription.prior g h)
local notation "Z₀" => _root_.IssuedMaxwell.ElectedPrescription.issued g h

open Structure1
theorem kernel (x : Stage 3) :
    (P₀).triangle.firstConnected GC x.val =
    YangMills.MSbar.Position.triangleKernel GC P₀ 1 x.val := by
  have leading : Dframe.meteor μ₀ M₀ 6 x.val 0 = scene x.val 6 := Dframe.limit_lead μ₀ M₀ x.property
  have tri : PowerSeries.coeff 1 (Reg.State.chooseL μ₀ (Z₀).store M₀ 6) ∈ Tri g.core 6 := by
    dsimp only [Reg.State.chooseL]
    rw [pos_decked _ (by decide)]
    exact AxesTangent.TriG 6 (Reg.State.root μ₀ (Z₀).store M₀ 6 1)
  have fr := Rose.tangent (Z₀).scheme (_root_.IssuedMaxwell.ElectedPrescription.simple g h)
    (Dframe.meteor μ₀ M₀ 6 x.val) leading x.property
  have screen := Rose.tangent (Z₀).scheme (_root_.IssuedMaxwell.ElectedPrescription.simple g h)
    (Reg.State.wall μ₀ (Z₀).store M₀ 6 x.val) (Reg.State.spirit μ₀ (Z₀).store M₀ x.val x.property) x.property
  rw [PostedAppointedFirstResponse.bare h x, fr, PostedAppointedTriangleMoments.kernel h 1 x,
      Reg.Choice.trace, screen, Reg.State.wall,
      PostedAppointedFirstResponse.response _ _ (Reg.State.baseL μ₀ (Z₀).store M₀ 6)]
  rw [_root_.add_apply, leading, Rose.stamp_fee (lot _ _),
    Tornado.ignored (Z₀).scheme (_root_.IssuedMaxwell.ElectedPrescription.simple g h) x.val x.property (PowerSeries.coeff 1 (Reg.State.chooseL μ₀ (Z₀).store M₀ 6)) tri,
    mul_zero, add_zero]

theorem original :
    (∫ x : YM.Points 3, (P₀).triangle.profile x * (P₀).triangle.firstConnected GC x) =
    YangMills.MSbar.Position.triangleAmplitude GC P₀ 1 := by
  apply YM.Test.apply_eq
  intro x hx
  exact kernel h ⟨x, hx⟩
end IssuedBridge.PostedAppointedFirstTangent
end
