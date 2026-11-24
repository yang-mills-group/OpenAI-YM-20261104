import YM.Integration.WilsonGraphMeasuredCompactCorrelation
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.ConstructedGroupGraphSum
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PublishedGraphSumAgreement

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.Answer.ContinuumLimit

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

open YangMills YangMills.Wilson
open _root_.IssuedBridge
open YangMills YangMills.Wilson
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
open YM.Answer.ContinuumLimit.Vision
open Frames Frames.Cortex Dancer Belfry Belfry.Classroom Belfry.ScaleFits Scale Level GroupS
open SeatsW
universe u
variable {g : YangMills.GaugeGroup} {R : Run g.core}
variable {H : g.core.Simple} {ε : ℝ} {e : Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}


open YM.Integration.WilsonGraphStandaloneCorrelation (cutoff within converted)

theorem publicMeasuredOnPerspective (V : Vision E ξ) (Z : WilsonPrescription g.core)
    {lamp : Bool} (Q : Perspective H Z lamp) (standalone : Vision.StandaloneCorrelation V Z Q.MS) :
    (cT Z < 0 ∧ ∀ r : ℝ, cT Z * V.T Z r = (Signal V Z r).re) ∧
      MeasuredMixedCompact V Z Q.MS Q.matching := by
  refine ⟨⟨standalone.negative, standalone.measured⟩, ?_⟩
  apply publicMixedCompact (R := E.paths) V Z Q.MS Q.matching standalone
  exact (SourceOnlyGraphSum.originalAgreement (R := E.paths) Z Q.MS (Teller.logNu 1)).mpr
    (SourceOnlyGraphSum.atMatch Z Q.MS Q.matching (Teller.logNu 1))

theorem publicMeasuredConstructedGroup (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (ε : ℝ) (hp : 0 < ε) (e : Axis) (O : OrderS g.core) :
    let H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ E : Construction.{u} H ε e O, ∀ ξ : Extraction.Order, ∃ V : Vision E ξ,
      ∀ lamp : Bool, ∃ Q : Perspective H Z lamp, Q.MS = A ∧
        Vision.StandaloneCorrelation V Z A ∧ SourceOnlyGraphSum.EveryCoefficient Z A (Teller.logNu 1) ∧
        (cT Z < 0 ∧ ∀ r : ℝ, cT Z * V.T Z r = (Signal V Z r).re) ∧
        MeasuredMixedCompact V Z Q.MS Q.matching := by
  dsimp only
  obtain ⟨E, elected⟩ := SourceOnlyGraphSum.constructedGroup g hg ε hp e O
  refine ⟨E, ?_⟩
  intro ξ
  obtain ⟨V, each⟩ := elected ξ
  refine ⟨V, ?_⟩
  intro lamp
  obtain ⟨Q, datum, full, coefficient⟩ := each lamp
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  have onThis : Vision.StandaloneCorrelation V Z Q.MS := by
    rw [datum]
    exact full
  exact ⟨Q, datum, full, coefficient, publicMeasuredOnPerspective V Z Q onThis⟩

end YM.Answer.ContinuumLimit
end

