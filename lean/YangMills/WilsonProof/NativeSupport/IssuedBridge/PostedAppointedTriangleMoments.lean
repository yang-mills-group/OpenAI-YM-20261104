import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedRawFrame
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedRawMoments
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedTriangleFaces
noncomputable section
namespace IssuedBridge.PostedAppointedTriangleMoments
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

theorem face (I : Finset (Fin 3)) (j : ℕ) (x : Stage 3) :
    YangMills.MSbar.Position.rawMoment GC P₀ 6 j 3 ((P₀).triangle.face I) x.val =
    Reg.State.wall μ₀ (Z₀).store M₀ 6 x.val j ((P₀).triangle.face I) := by
  unfold YangMills.MSbar.Position.rawMoment
  rw [PostedAppointedRawFrame.through h 6 j]
  exact PostedNamedRawMoments.measured Z₀ 3 6 j _ x

theorem cumulant (m : Finset (Fin 3) → PowerSeries ℂ) :
    YangMills.MSbar.Position.connectedThree m = Rose.b3 m := by
  unfold YangMills.MSbar.Position.connectedThree Rose.b3
  simp only [two_smul]
  ring

theorem kernel (k : ℕ) (x : Stage 3) :
    YangMills.MSbar.Position.triangleKernel GC P₀ k x.val =
    PowerSeries.coeff k (Reg.Choice.trace μ₀ M₀ (Z₀).store x.val) := by
  rw [YangMills.MSbar.Position.triangleKernel, cumulant, Reg.Choice.trace]
  apply congrArg (fun m => PowerSeries.coeff k (Rose.b3 m))
  funext I
  apply PowerSeries.ext
  intro j
  simp only [Rose.batchT, PowerSeries.coeff_mk]
  rw [← PostedAppointedTriangleFaces.original g h I]
  exact face h I j x

theorem original (k : ℕ) :
    YangMills.MSbar.Position.triangleAmplitude GC P₀ k =
    YM.Test.applyTo (P₀).triangle.profile (fun x => PowerSeries.coeff k (Reg.Choice.trace μ₀ M₀ (Z₀).store x)) := by
  unfold YangMills.MSbar.Position.triangleAmplitude
  apply YM.Test.apply_eq
  intro x hx
  exact kernel h k ⟨x, hx⟩

end IssuedBridge.PostedAppointedTriangleMoments
end
