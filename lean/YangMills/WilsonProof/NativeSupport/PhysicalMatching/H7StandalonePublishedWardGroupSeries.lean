import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedWardGroupGroundSeries
import YM.Integration.WilsonGraphPublishedStressColumns
import YM.Integration.WilsonElectedFourthPowerClock

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

theorem onPublishedVolume (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (phase : Option (wardHierarchy V).Character)
    (o : YangMills.Spacetime) (pupils : Pupils) 
    (rows : ∀ i j, matrixCoefficients Z Q pupils 0 i j =
      H7IndependentFourMaxwellWardReadings.leading
        (matrixCoefficients Z Q pupils 0 3 1) (matrixCoefficients Z Q pupils 0 3 2) i j)
    : YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1))
        (H7StandaloneAppointedWardStressSeries.selected Z Q pupils (matrixCoefficients Z Q pupils 0)) ∧
      YangMills.Matching.CorrelationOnly.namedStress
        (ElectedMeasurement.publicMeasurement (H7StandaloneAppointedWardGroupSeries.publicSimple H) V Z Q)
        (H7StandaloneAppointedWardStressSeries.selected Z Q pupils (matrixCoefficients Z Q pupils 0)) := by
  apply atIndependentPupils V Z Q
    (referenceCapped (R := E.paths) Z V Q (atOneMatch E.paths Z Q (FVA2.Teller.logNu 1)))
    phase o pupils rows
  · intro k
    exact YM.Integration.WilsonElectedFourthPowerClock.ratio V Z Q k
  · exact PhysicalMatching.H7StandaloneAppointedPublicWardRows.measuredStressColumns V Z Q

end PhysicalMatching.H7StandaloneAppointedWardGroupSeries
end

