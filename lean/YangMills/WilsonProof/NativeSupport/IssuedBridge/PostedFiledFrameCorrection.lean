import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFiledFrameDiagonal
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFiledFrameProduct
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPositionGradeProjection
noncomputable section
namespace IssuedBridge.PostedFiledFrameCorrection
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

theorem original (μ : ℝ) : (W μ).adjustment = Series.adjustment B (nativeFrame Z raw μ) := by
  let H := matched.details.toServed.toPosted.toQuoted.toContract.toMission.born
  funext d k
  let A := Measure.liftT Z.criterion μ raw d
  let C := Scale.diagonal A
  have adj : Measure.adjust Z.scheme Z.criterion d = Scale.mirror A * C :=
    Measure.matchU Z.scheme Z.criterion μ raw σ simple H.Taylor H.still H.base _
      (Measure.adj Z.scheme Z.criterion μ raw σ simple H.Taylor H.still H.base)
  have mkA : PowerSeries.mk (fun j => PowerSeries.coeff j A) = A := by
    apply PowerSeries.ext
    intro j
    exact PowerSeries.coeff_mk j _
  have inv (j : ℕ) : Series.inverseFrame B (nativeFrame Z raw μ) d j = PowerSeries.coeff j (Scale.mirror A) :=
    congrArg (fun t => PowerSeries.coeff j (PowerSeries.invOfUnit t 1)) mkA
  have gr (j : ℕ) : Series.gradeFrame B (nativeFrame Z raw μ) d j = PowerSeries.coeff j C := by
    change Matching.Grade.diagonal B d (PowerSeries.coeff j A) = _
    rw [PostedPositionGradeProjection.original]
    symm
    exact PowerSeries.coeff_mk j (fun i => Level.diag (PowerSeries.coeff i A))
  change PowerSeries.coeff k (Measure.adjust Z.scheme Z.criterion d) = _
  rw [adj]
  unfold Series.adjustment Series.cauchy
  simp_rw [inv, gr]
  let term := fun i : ℕ => PowerSeries.coeff i (Scale.mirror A) * PowerSeries.coeff (k-i) C
  change PowerSeries.coeff k (Scale.mirror A * C) = ∑ i : Fin (k+1), term i.val
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Fin.sum_univ_eq_sum_range]
end IssuedBridge.PostedFiledFrameCorrection
end
