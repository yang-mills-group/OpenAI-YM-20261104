import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedWardStressSeries
import YM.Integration.WilsonGraphAppointedWardGroundMatrix
import YM.Integration.WilsonGraphAppointedMeasurementLaws

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace PhysicalMatching.H7StandaloneAppointedWardGroupSeries
open YM YM.Answer YM.Answer.ContinuumLimit


open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Entree Future
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped BigOperators Classical ContDiff Topology

open YangMills
open _root_.IssuedBridge
open YangMills
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical
open MS MS.Land MS.Fleet FVA2.Scale WilsonViewerReportingGrid WilsonThermometerWeakMeasuredSeries
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open YM.FVA2.Scale YM.MS YM.MS.Fleet YM.MS.Land YangMills.Matching
open YangMills.Matching
universe u
variable {g : YangMills.GaugeGroup} {R : Run g.core}
variable {H : g.core.Simple} {ε : ℝ} {e : YM.Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}



open YM.Maxwell.Free YM.Maxwell.Wick YM.XSpace.Normalize
open scoped BigOperators Classical

open MeasureTheory
open PhysicalMatching.H7StandaloneAppointedPublicWardRows PhysicalMatching.H7StandaloneFourSmearedWardReadings
open PhysicalMatching.H7StandaloneAppointedWardBalance
open scoped BigOperators Classical Topology


open PhysicalMatching.H7StandaloneFiniteWardMatrix PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
open PhysicalMatching.H7StandaloneWardSeriesDivision
open YM.Integration.WilsonGraphPublishedShapeEstimate


open PhysicalMatching.H7StandaloneWardTensorPolynomial

open PhysicalMatching.H7StandaloneAppointedWardStressSeries

theorem publicSimple (h : g.core.Simple) : g.IsSimple := by
  have he : g.core.lie = g.lieAlgebra := by
    ext X
    exact (g.generates X).symm
  rw [YM.Gauge.Simple, he] at h
  exact h

theorem electedClock (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true) :
    (∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ElectedMeasurement.clock V Z r) ∧
      Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0) :=
  ⟨(V.certificate Q).calendar.clock.positive,
    YM.Trace.Pilot.Coupling.conforms H (V.certificate Q).calendar.clock⟩

theorem filedRead (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (n : ℕ) (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (k : ℕ)
    (x : YangMills.Points n) (hx : x ∈ conf n) :
    (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1)).correlation
      (_root_.IssuedMaxwell.GraphCoefficients.issued g) k (publicLetters d v) x =
        groupCoefficient Z Q d v k x :=
  (YM.Integration.WilsonGraphAppointedWardGroundMatrix.converted
    (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1))
    k (publicLetters d v) x hx).symm

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character)
    (o : YangMills.Spacetime) (pupils : Pupils) (B : Matrix4)
    (left : ∀ x, act B (act (matrixCoefficients Z Q pupils 0) x) = x)
    (right : ∀ x, act (matrixCoefficients Z Q pupils 0) (act B x) = x)
    (fourth : ∀ k : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^k)
      (𝓝[>] 0) (𝓝 0))
    (span : ∀ᶠ r : ℝ in 𝓝[>] 0, ∃ v : Coords, ∀ a b,
      measuredStress V Z r a b = ∑ i, v i • columns H a b i)
    (ground : rhsCoefficients Z Q pupils 0 = act (matrixCoefficients Z Q pupils 0) ![0,0,0,1])
    : YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1))
        (H7StandaloneAppointedWardStressSeries.selected Z Q pupils B) ∧
      YangMills.Matching.CorrelationOnly.namedStress
        (ElectedMeasurement.publicMeasurement (publicSimple H) V Z Q)
        (H7StandaloneAppointedWardStressSeries.selected Z Q pupils B) := by
  exact H7StandaloneAppointedWardStressSeries.original V Z Q shapes phase o pupils B
    left right (electedClock V Z Q).1 (electedClock V Z Q).2 fourth span ground
    (_root_.IssuedMaxwell.GraphCoefficients.issued g)
    (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1))
    (filedRead Z Q) (ElectedMeasurement.publicMeasurement (publicSimple H) V Z Q) (fun _ => rfl) rfl

end PhysicalMatching.H7StandaloneAppointedWardGroupSeries
end

