import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedTriangleMoments
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedClockScale
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedScreenBalance
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
noncomputable section
namespace IssuedBridge.PostedAppointedClockReading
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

open YangMills.MSbar.Position (rawFrame framePrefix)

theorem amplitude (k : ℕ) : YangMills.MSbar.Position.triangleAmplitude GC P₀ k =
    PowerSeries.coeff k (Reg.Choice.sky μ₀ (Z₀).criterion M₀) := by
  rw [PostedAppointedTriangleMoments.original h k, Reg.Choice.sky, PowerSeries.coeff_mk]
  unfold YM.Test.applyTo
  apply integral_congr_ae
  filter_upwards [] with x
  rw [PostedAppointedClockScale.profile h x]
  rfl

theorem reading (k : ℕ) : YangMills.MSbar.Position.measuredCoupling GC P₀ k =
    PowerSeries.coeff k (Reg.Choice.choice μ₀ (Z₀).criterion M₀) := by
  rw [YangMills.MSbar.Position.measuredCoupling, amplitude h k, amplitude h 0,
    PostedAppointedClockScale.centered]

theorem signed :
    (∀ k, (YangMills.MSbar.Position.positionReading GC P₀ k : ℂ) =
        YangMills.MSbar.Position.measuredCoupling GC P₀ k) ∧
    YangMills.MSbar.Position.positionReading GC P₀ 1 = 1 := by
  obtain ⟨s,m⟩ := (_root_.IssuedMaxwell.ElectedPrescription.original g h).2.2.2.2 false
  let H := m.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have real := Reg.Choice.token μ₀ (Z₀).scheme (Z₀).criterion s M₀
    (_root_.IssuedMaxwell.ElectedPrescription.simple g h) H.Taylor H.still H.base
  have lead := Reg.Choice.stance μ₀ (Z₀).scheme (Z₀).criterion s M₀
    (_root_.IssuedMaxwell.ElectedPrescription.simple g h) H.Taylor H.still H.base
  constructor
  · intro k
    rw [YangMills.MSbar.Position.positionReading, reading h k]
    have conjugate : (starRingEnd ℂ) (PowerSeries.coeff k (Reg.Choice.choice μ₀ (Z₀).criterion M₀)) = PowerSeries.coeff k (Reg.Choice.choice μ₀ (Z₀).criterion M₀) := by
      simpa only [PowerSeries.coeff_map] using congrArg (PowerSeries.coeff k) real
    have imaginary := congrArg Complex.im conjugate
    simp only [Complex.conj_im] at imaginary
    apply Complex.ext
    · rfl
    · change 0 = (PowerSeries.coeff k (Reg.Choice.choice μ₀ (Z₀).criterion M₀)).im
      linarith
  · rw [YangMills.MSbar.Position.positionReading, reading h 1, lead]
    rfl

theorem tree : YangMills.MSbar.Position.triangleAmplitude GC P₀ 1 = ((P₀).triangle.cT : ℂ) := by
  have E := (signed h).1 1
  rw [(signed h).2, Complex.ofReal_one, YangMills.MSbar.Position.measuredCoupling,
    if_neg (by decide : (1:ℕ) ≠ 0), sub_zero] at E
  have nz := Complex.ofReal_ne_zero.mpr (PostedAppointedClockScale.nonzero h)
  exact (div_eq_one_iff_eq nz).mp E.symm
theorem original (k : ℕ) :
    YangMills.MSbar.Position.triangleAmplitude GC P₀ k =
        PowerSeries.coeff k (Reg.Choice.sky μ₀ (Z₀).criterion M₀) ∧
    YangMills.MSbar.Position.measuredCoupling GC P₀ k =
        PowerSeries.coeff k (Reg.Choice.choice μ₀ (Z₀).criterion M₀) ∧
    (∀ j, (YangMills.MSbar.Position.positionReading GC P₀ j : ℂ) =
        YangMills.MSbar.Position.measuredCoupling GC P₀ j) ∧
    YangMills.MSbar.Position.positionReading GC P₀ 1 = 1 :=
  ⟨amplitude h k, reading h k, (signed h).1, (signed h).2⟩

end IssuedBridge.PostedAppointedClockReading
end

