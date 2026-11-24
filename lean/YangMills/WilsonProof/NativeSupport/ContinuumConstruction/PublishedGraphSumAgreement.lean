import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.MatchGraphSum
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.NominatedGraphSum

set_option autoImplicit false
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
universe u
variable {g : YangMills.GaugeGroup} {R : Run g.core}
variable {H : g.core.Simple} {ε : ℝ} {e : Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}


namespace SourceOnlyGraphSum
theorem originalAgreement (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core))) (μ : ℝ) :
    AllAppointedGraphSums R Z A μ ↔ EveryCoefficient Z A μ := by
  constructor <;> intro h n l d v within x k
  all_goals
    have legs : commonCaps (PostedMeasuredCompactCorrelation.leaves (R:=R) d v) within =
        (fun i => XSpace.Normalize.up (within i) (v i)) :=
      funext (fun i => PostedNestedFieldColumns.raised (R:=R) d v within i)
    have coupling : _root_.IssuedBridge.PostedRealFiledCoupling.coefficient Z A μ =
        _root_.ContinuumConstruction.MatchAllocation.PostedRealFiledCoupling.coefficient Z A μ :=
      funext (fun j => rfl)
    simpa only [legs, AppointedGraphSum, screen, coupling] using h d v within x k
end SourceOnlyGraphSum
end YM.Answer.ContinuumLimit
