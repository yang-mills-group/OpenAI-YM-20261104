import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedSignedCoordinateTurn
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralAdjustment

noncomputable section
namespace IssuedBridge.PostedAdjustmentSymmetries
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
open PostedBilateralAdjustment
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

private theorem fixed {d : ℕ} (p : (maxwellReference g).sector d) :
    (∀ m, (MvPolynomial.coeff m p.val).im = 0) ↔ XSpace.Normalize.reel d p = p := by
  constructor
  · intro hp
    apply Subtype.ext
    change MvPolynomial.map (starRingEnd ℂ) p.val = p.val
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_map]
    exact Complex.conj_eq_iff_im.mpr (hp m)
  · intro hp m
    apply Complex.conj_eq_iff_im.mp
    have eq := congrArg (fun a : (maxwellReference g).sector d => MvPolynomial.coeff m a.val) hp
    change MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) p.val) = _ at eq
    simpa only [MvPolynomial.coeff_map] using eq


theorem real (d : ℕ) (t : ℝ) (p : (maxwellReference g).sector d)
    (hp : ∀ m, (MvPolynomial.coeff m p.val).im = 0) :
    ∀ m, (MvPolynomial.coeff m (value Z d t p).val).im = 0 := by
  have comm := (limb Z d t).property.2.2.1 p
  rw [(fixed p).1 hp] at comm
  have hc := (fixed _).2 comm.symm
  have added (a b : WickPol g.core) (m : _) :
      (MvPolynomial.coeff m (a+b)).im = (MvPolynomial.coeff m a).im + (MvPolynomial.coeff m b).im := by
    rw [MvPolynomial.coeff_add,Complex.add_im]
  intro m
  exact (added p.val ((limb Z d t).val p).val m).trans ((congrArg₂ (· + ·) (hp m) (hc m)).trans (zero_add _))

theorem original (t : ℝ) (d : ℕ) (π : Equiv.Perm YM.Axis) (sgn : YM.Axis → ℝ)
    (U : E4 ≃ₗᵢ[ℝ] E4) (hs : ∀ a, sgn a = 1 ∨ sgn a = -1)
    (hU : ∀ a, U (basis a) = sgn a • basis (π a))
    (p q : (maxwellReference g).sector d)
    (source : Matching.RelatedByAxes (maxwellReference g) π sgn U p.val q.val) :
    Matching.RelatedByAxes (maxwellReference g) π sgn U
      (value Z d t p).val
      (value Z d t q).val := by
  let s := PostedSignedCoordinateTurn.axes π sgn
  have eq : ori s.ortho d p = q := Subtype.ext ((related π sgn U hs hU _ _).1 source)
  have comm := (limb Z d t).property.2.2.2 s p
  rw [eq] at comm
  have rhs := (related π sgn U hs hU _ _).2 (congrArg Subtype.val comm.symm)
  intro A A' rot
  change probe A' ((show WickPol g.core from p.val) + ((limb Z d t).val p).val) = probe A ((show WickPol g.core from q.val) + ((limb Z d t).val q).val)
  rw [map_add,map_add]
  exact congrArg₂ (· + ·) (source A A' rot) (rhs A A' rot)
end IssuedBridge.PostedAdjustmentSymmetries
end
