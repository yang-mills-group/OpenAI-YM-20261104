import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedPinFrame

noncomputable section
namespace IssuedBridge.PostedAppointedFieldBank
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

def column (μ : ℝ) (d k : ℕ) : (maxwellReference g).sector d →ₗ[ℂ] (maxwellReference g).sector d :=
  PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d)
include matched in
theorem nested (μ : ℝ) (d e k : ℕ) (p : (maxwellReference g).sector d) (q : (maxwellReference g).sector e)
    (same : p.val = q.val) : (column Z raw μ d k p).val = (column Z raw μ e k q).val := by
  have forward {a b : ℕ} (le : a ≤ b) (v : (maxwellReference g).sector a) (w : (maxwellReference g).sector b)
      (eq : v.val = w.val) : (column Z raw μ a k v).val = (column Z raw μ b k w).val := by
    have transport := matched.frameCompat μ a b le k v
    have vw : XSpace.Normalize.up le v = w := Subtype.ext eq
    rw [vw] at transport
    exact (congrArg Subtype.val transport).symm
  rcases le_total d e with de | ed
  · exact forward de p q same
  · exact (forward ed q p same.symm).symm
include matched in
theorem original (μ : ℝ) (d : ℕ) :
    column Z raw μ d 0 = LinearMap.id ∧
    (∀ k, Level.Graded (column Z raw μ d k)) ∧
    (∀ k, column Z raw μ d (k+1) ∈ XSpace.Normalize.Change g.core d) ∧
    (∀ k (p : (maxwellReference g).sector d), p.val = 1 → column Z raw μ d (k+1) p = 0) := by
  have base := (matched.frame μ d).1
  refine ⟨?_, (matched.frame μ d).2, fun k => base.high _ (by omega), ?_⟩
  · apply LinearMap.ext
    intro a
    change (PowerSeries.coeff 0 (Measure.Z Z.scheme Z.criterion μ raw d)) a = a
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, base.lead]
    rfl
  intro k p h
  have eq : p = XSpace.Normalize.leaf g.core d := Subtype.ext h
  rw [eq]
  exact (base.high (k+1) (by omega)).1
end IssuedBridge.PostedAppointedFieldBank
end
