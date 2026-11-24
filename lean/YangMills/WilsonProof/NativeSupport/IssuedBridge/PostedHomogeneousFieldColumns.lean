import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedPinFrame

noncomputable section
namespace IssuedBridge.PostedHomogeneousFieldColumns
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

open YM.Maxwell.Wick
include matched in
theorem original (μ : ℝ) (d h k : ℕ) (p : (maxwellReference g).sector d)
    (hp : YangMills.Matching.Homogeneous (maxwellReference g) h p.val) :
    YangMills.Matching.Homogeneous (maxwellReference g) h
      ((PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d)) p).val := by
  let T := PowerSeries.coeff k (Measure.Z Z.scheme Z.criterion μ raw d)
  have source : MvPolynomial.IsWeightedHomogeneous scaleW p.val h := by
    intro m hm
    exact hp m (MvPolynomial.mem_support_iff.mpr hm)
  have result : MvPolynomial.IsWeightedHomogeneous scaleW (T p).val h := by
    by_cases within : h ≤ d
    · let i : Fin (d+1) := ⟨h, by omega⟩
      have same : Level.proj i p = p := Subtype.ext source.weightedHomogeneousComponent_same
      have diagonal := Level.diagonals p i T
      have grade : Level.diag T = T := (matched.frame μ d).2 k
      rw [grade, same] at diagonal
      rw [diagonal]
      exact (XSpace.Normalize.part d h (T p)).property.2
    · have vanished := congrArg Subtype.val (XSpace.Normalize.part_zero (by omega : d < h) p)
      change XSpace.Normalize.engineering h g.core p.val = 0 at vanished
      have zero : (show Sec g.core d from p) = 0 :=
        Subtype.ext (source.weightedHomogeneousComponent_same.symm.trans vanished)
      have image : T (show Sec g.core d from p) = 0 :=
        (congrArg T zero).trans T.map_zero
      rw [image]
      exact MvPolynomial.isWeightedHomogeneous_zero ..
  intro m hm
  exact result (MvPolynomial.mem_support_iff.mp hm)
end IssuedBridge.PostedHomogeneousFieldColumns
end
