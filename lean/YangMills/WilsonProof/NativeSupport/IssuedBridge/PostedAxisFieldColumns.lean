import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedSignedCoordinateTurn

noncomputable section
namespace IssuedBridge.PostedAxisFieldColumns
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

private theorem related (σ : Equiv.Perm YM.Axis) (sign : YM.Axis → ℝ)
    (U : E4 ≃ₗᵢ[ℝ] E4) (hs : ∀ a, sign a = 1 ∨ sign a = -1)
    (hU : ∀ a, U (basis a) = sign a • basis (σ a))
    (p q : (maxwellReference g).toCoordinates.Pol) :
    Matching.RelatedByAxes (maxwellReference g) σ sign U p q ↔
      reflectPol (PostedSignedCoordinateTurn.axes σ sign).ortho p = q := by
  let s := (PostedSignedCoordinateTurn.axes σ sign).ortho
  constructor
  · intro relation
    apply equalPol
    intro A
    rw [reflects_eval]
    exact relation A (fun j => solutionTurn s⁻¹ (A j))
      (PostedSignedCoordinateTurn.original σ sign U hs hU A)
  · intro equal A A' rotated
    have same : A' = fun j => solutionTurn s⁻¹ (A j) := by
      funext j
      apply Subtype.ext
      funext a b
      apply ContinuousMultilinearMap.ext
      intro v
      exact (rotated j a b v).trans
        (PostedSignedCoordinateTurn.original σ sign U hs hU A j a b v).symm
    subst A'
    change probe (fun j => solutionTurn s⁻¹ (A j)) p = probe A q
    exact (reflects_eval s A p).symm.trans (congrArg (probe A) equal)

include matched in
theorem original (μ : ℝ) (d k : ℕ) (π : Equiv.Perm YM.Axis) (sgn : YM.Axis → ℝ)
    (U : E4 ≃ₗᵢ[ℝ] E4) (hs : ∀ a, sgn a = 1 ∨ sgn a = -1)
    (hU : ∀ a, U (basis a) = sgn a • basis (π a))
    (p q : (maxwellReference g).sector d)
    (source : Matching.RelatedByAxes (maxwellReference g) π sgn U p.val q.val) :
    Matching.RelatedByAxes (maxwellReference g) π sgn U
      ((PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d)) p).val
      ((PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d)) q).val := by
  have base := (matched.frame μ d).1
  cases k with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, base.lead]
    exact source
  | succ k =>
    let s := PostedSignedCoordinateTurn.axes π sgn
    have column : ori s.ortho d p = q :=
      Subtype.ext ((related π sgn U hs hU p.val q.val).1 source)
    apply (related π sgn U hs hU _ _).2
    have comm := (base.high (k+1) (by omega)).2.2.2 s p
    rw [column] at comm
    exact congrArg Subtype.val comm.symm
end IssuedBridge.PostedAxisFieldColumns
end
