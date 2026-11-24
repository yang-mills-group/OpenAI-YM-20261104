import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedCouplingPowers
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFiledFrameProduct
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPositionGradeProjection
noncomputable section
namespace IssuedBridge.PostedScreenedReparametrization
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


open PostedFiledFrameProduct (nativeFrame)

def screened (μ : ℝ) : Series.Frame B := fun d j =>
  PowerSeries.coeff j (Reg.State.chooseL μ Z.store raw d)

theorem original (μ : ℝ) :
    nativeFrame Z raw μ = Series.reparametrize B (W μ).conversion.f (screened Z raw μ) := by
  funext d k
  let q := Measure.f Z.criterion μ raw
  let S := Reg.State.chooseL μ Z.store raw d
  let f := PostedRealFiledCoupling.coefficient Z raw μ
  have real : ∀ i, PowerSeries.coeff i q = (f i : ℂ) :=
    (PostedRealFiledCoupling.original Z raw matched μ).1
  have indices : Finset.Iic k = Finset.range (k + 1) := by
    ext i
    simp
  change PowerSeries.coeff k (Reg.Point.stepV q S) =
    ∑ j : Fin (k+1), (Matching.couplingPower f j.val k : ℂ) • PowerSeries.coeff j.val S
  rw [Reg.Point.stepV, PowerSeries.coeff_mk, MS.Book.Program.rules, indices,
    ← Fin.sum_univ_eq_sum_range (fun j => MS.Book.Program.cut q j k • PowerSeries.coeff j S) (k+1)]
  exact Finset.sum_congr rfl fun j _ => by rw [PostedCouplingPowers.original q f real j k]
end IssuedBridge.PostedScreenedReparametrization
end
