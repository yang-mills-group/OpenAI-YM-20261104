import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedPinFrame

noncomputable section
namespace IssuedBridge.PostedRealFieldColumns
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

include matched in
theorem original (μ : ℝ) (d k : ℕ) (p : (maxwellReference g).sector d)
    (hp : ∀ m, (MvPolynomial.coeff m p.val).im = 0) :
    ∀ m, (MvPolynomial.coeff m
      ((PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d)) p).val).im = 0 := by
  have base := (matched.frame μ d).1
  cases k with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, base.lead]
    exact hp
  | succ k =>
    apply (fixed _).2
    have commute := (base.high (k+1) (by omega)).2.2.1 p
    rw [(fixed p).1 hp] at commute
    exact commute.symm
end IssuedBridge.PostedRealFieldColumns
end
