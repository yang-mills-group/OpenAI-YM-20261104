import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedTriangleMoments
noncomputable section
namespace IssuedBridge.PostedAppointedFreeTriangle
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

theorem face (x : Stage 3) (I : Finset (Fin 3)) (hi : I.Nonempty) :
    PowerSeries.constantCoeff (Rose.batchT (Reg.State.wall μ₀ (Z₀).store M₀ 6 x.val) I) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Rose.batchT, PowerSeries.coeff_mk,
      Reg.State.spirit μ₀ (Z₀).store M₀ x.val x.property]
  exact Rose.silent (Z₀).scheme (_root_.IssuedMaxwell.ElectedPrescription.simple g h) x.property I hi

theorem kernel (x : Stage 3) : YangMills.MSbar.Position.triangleKernel GC P₀ 0 x.val = 0 := by
  rw [PostedAppointedTriangleMoments.kernel h 0 x, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold Reg.Choice.trace Rose.b3
  simp only [two_smul, map_add, map_sub, map_mul]
  rw [face h x Finset.univ (by decide), face h x {0,1} (by decide),
      face h x {0,2} (by decide), face h x {1,2} (by decide),
      face h x {0} (by decide), face h x {1} (by decide), face h x {2} (by decide)]
  ring

theorem original : YangMills.MSbar.Position.triangleAmplitude GC P₀ 0 = 0 := by
  calc
    _ = YM.Test.applyTo (P₀).triangle.profile (fun _ => (0 : ℂ)) := by
      apply YM.Test.apply_eq
      intro x hx
      exact kernel h ⟨x, hx⟩
    _ = 0 := by simp [YM.Test.applyTo]
end IssuedBridge.PostedAppointedFreeTriangle
end
