import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFirstTangent
noncomputable section
namespace IssuedBridge.PostedSubmittedTriangleSlope
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
theorem bare (t : YangMills.MSbar.Position.Triangle (_root_.IssuedMaxwell.Reference.issued g)) (x : Stage 3) :
    t.firstConnected GC x.val =
    PowerSeries.coeff 1 (Rose.b3 (Rose.batchT (Dframe.meteor μ₀ M₀ 6 x.val))) := by
  rw [YangMills.MSbar.Position.Triangle.firstConnected, PostedAppointedTriangleMoments.cumulant]
  apply congrArg (fun m => PowerSeries.coeff 1 (Rose.b3 m))
  funext I
  apply PowerSeries.ext
  intro j
  simp only [Rose.batchT, PowerSeries.coeff_mk]
  rw [← PostedAppointedTriangleFaces.faces g t I]
  exact PostedNamedRawMoments.cofiled 3 6 j x _
include h in
theorem kernel (t : YangMills.MSbar.Position.Triangle (_root_.IssuedMaxwell.Reference.issued g)) (Z : WilsonPrescription g.core) (x : Stage 3) :
    t.firstConnected GC x.val =
    PowerSeries.coeff 1 (Reg.Choice.trace μ₀ M₀ Z.store x.val) := by
  have leading : Dframe.meteor μ₀ M₀ 6 x.val 0 = scene x.val 6 := Dframe.limit_lead μ₀ M₀ x.property
  have tri : PowerSeries.coeff 1 (Reg.State.chooseL μ₀ Z.store M₀ 6) ∈ Tri g.core 6 := by
    dsimp only [Reg.State.chooseL]
    rw [pos_decked _ (by decide)]
    exact AxesTangent.TriG 6 (Reg.State.root μ₀ Z.store M₀ 6 1)
  have fr := Rose.tangent Z.scheme (_root_.IssuedMaxwell.ElectedPrescription.simple g h)
    (Dframe.meteor μ₀ M₀ 6 x.val) leading x.property
  have screen := Rose.tangent Z.scheme (_root_.IssuedMaxwell.ElectedPrescription.simple g h)
    (Reg.State.wall μ₀ Z.store M₀ 6 x.val) (Reg.State.spirit μ₀ Z.store M₀ x.val x.property) x.property
  rw [bare t x, fr,
      Reg.Choice.trace, screen, Reg.State.wall,
      PostedAppointedFirstResponse.response _ _ (Reg.State.baseL μ₀ Z.store M₀ 6)]
  rw [_root_.add_apply, leading, Rose.stamp_fee (lot _ _),
    Tornado.ignored Z.scheme (_root_.IssuedMaxwell.ElectedPrescription.simple g h) x.val x.property (PowerSeries.coeff 1 (Reg.State.chooseL μ₀ Z.store M₀ 6)) tri,
    mul_zero, add_zero]

include h in
theorem original (P : PositionPrescription (_root_.IssuedMaxwell.Reference.issued g))
    (hp : Admissible P) : P.triangle.RawSlopeAgrees GC := by
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g h
  let Z := _root_.IssuedMaxwell.AppointedPrescription.issued simple P hp
  obtain ⟨_, _, _, _, image, price, matched⟩ := _root_.IssuedMaxwell.AppointedPrescription.original simple P hp
  obtain ⟨σ, m⟩ := matched false
  let H := m.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have scale : Rose.c_T Z.criterion = P.triangle.cT := price
  have income : (∫ x : YM.Points 3, P.triangle.profile x * P.triangle.firstConnected GC x) =
      PowerSeries.coeff 1 (Reg.Choice.sky μ₀ Z.criterion M₀) := by
    rw [Reg.Choice.sky, PowerSeries.coeff_mk]
    calc
      _ = YM.Test.applyTo P.triangle.profile (fun x => PowerSeries.coeff 1 (Reg.Choice.trace μ₀ M₀ Z.store x)) := by
        apply YM.Test.apply_eq
        intro x hx
        exact kernel h P.triangle Z ⟨x,hx⟩
      _ = _ := by
        unfold YM.Test.applyTo
        apply integral_congr_ae
        filter_upwards with x
        rw [show Rose.test Z.criterion x = P.triangle.profile x from image x]
        rfl
  have lead := Reg.Choice.stance μ₀ Z.scheme Z.criterion σ M₀ simple H.Taylor H.still H.base
  have centered : PowerSeries.coeff 1 (Reg.Choice.choice μ₀ Z.criterion M₀) =
      PowerSeries.coeff 1 (Reg.Choice.sky μ₀ Z.criterion M₀) / (P.triangle.cT : ℂ) := by
    unfold Reg.Choice.choice Reg.Choice.tune
    rw [map_smul, map_sub, PowerSeries.coeff_C, if_neg (by decide : (1:ℕ) ≠ 0), sub_zero, scale]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact income.trans ((div_eq_one_iff_eq (Complex.ofReal_ne_zero.mpr hp.calibration.negative.ne)).mp
    (centered.symm.trans lead))
end IssuedBridge.PostedSubmittedTriangleSlope
end
