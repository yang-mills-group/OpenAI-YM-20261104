import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedBlindResidual
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedScreenBalance
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
noncomputable section
namespace IssuedBridge.PostedAppointedClockScale
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
theorem profile (x : YM.Points 3) : Rose.test (Z₀).criterion x = (P₀).triangle.profile x :=
  (_root_.IssuedMaxwell.ElectedPrescription.original g h).2.2.2.1 x

theorem price : Rose.c_T (Z₀).criterion = (P₀).triangle.cT :=
  (_root_.IssuedMaxwell.AppointedPrescription.original
    (_root_.IssuedMaxwell.ElectedPrescription.simple g h) P₀ H₀).2.2.2.2.2.1

theorem nonzero : (P₀).triangle.cT ≠ 0 := by
  rw [← price h]
  exact (Z₀).criterion.fresh.ne

theorem centered (k : ℕ) :
    PowerSeries.coeff k (Reg.Choice.choice μ₀ (Z₀).criterion M₀) =
    (PowerSeries.coeff k (Reg.Choice.sky μ₀ (Z₀).criterion M₀) -
      (if k = 0 then PowerSeries.coeff 0 (Reg.Choice.sky μ₀ (Z₀).criterion M₀) else 0)) /
        ((P₀).triangle.cT : ℂ) := by
  unfold Reg.Choice.choice Reg.Choice.tune
  rw [map_smul, map_sub, PowerSeries.coeff_C, price h]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem original : (∀ x : YM.Points 3, Rose.test (Z₀).criterion x = (P₀).triangle.profile x) ∧
    Rose.c_T (Z₀).criterion = (P₀).triangle.cT ∧ (P₀).triangle.cT ≠ 0 :=
  ⟨profile h, price h, nonzero h⟩

end IssuedBridge.PostedAppointedClockScale
end
