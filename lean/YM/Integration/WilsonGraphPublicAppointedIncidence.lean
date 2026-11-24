import YM.Integration.WilsonGraphPublicFiledCoefficient
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.NominatedGraphSum
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedConversion

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
universe u
variable {g : YangMills.GaugeGroup} {R : Run g.core}
variable {H : g.core.Simple} {ε : ℝ} {e : Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}


open YM.Integration.WilsonGraphStandaloneCorrelation (cutoff within converted)

theorem publicAppointedArray (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
    {σ : Prescription (Press.portDeck g.core)} {lamp : Bool} (matched : Main.Match Z H A σ lamp)
    {n : ℕ} (a : Fin n → YM.Integration.WilsonGraphStandaloneCorrelation.Label g)
    (x : Stage n) (k : ℕ) :
    converted (PostedAppointedConversion.filed Z A matched (Teller.logNu 1)) k a x.val =
      AppointedGraphSum Z A (Teller.logNu 1) (fun i => (a i).1) (fun i => (a i).2) (within a) x k := by
  exact YM.Integration.WilsonGraphPublicFiledCoefficient.filed
    (PostedAppointedConversion.filed Z A matched (Teller.logNu 1))
    (PostedRealFiledCoupling.coefficient Z A (Teller.logNu 1))
    (fun d j u => (PowerSeries.coeff j (Measure.Z Z.scheme Z.criterion (Teller.logNu 1) A d)) u)
    (fun _ => rfl) (fun _ _ _ => rfl) k a x.val

theorem publicFiledAt (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
    {σ : Prescription (Press.portDeck g.core)} {lamp : Bool} (matched : Main.Match Z H A σ lamp)
    (paid : AllAppointedGraphSums R Z A (Teller.logNu 1))
    {n : ℕ} (a : Fin n → YM.Integration.WilsonGraphStandaloneCorrelation.Label g)
    (x : Stage n) (k : ℕ) :
    Jury.fxt (Measure.outlook Z.scheme Z.criterion (cutoff a)) x.val k
      (commonCaps (PostedMeasuredCompactCorrelation.leaves (R:=R) (fun i => (a i).1)
        (fun i => (a i).2)) (within a)) =
      converted (PostedAppointedConversion.filed Z A matched (Teller.logNu 1)) k a x.val :=
  (paid (fun i => (a i).1) (fun i => (a i).2) (within a) x k).trans
    (publicAppointedArray Z A matched a x k).symm

/-- The elected vision and its same prescription supply the public coefficient for every separated
mixed-grade word, at every order and on the original signed clock. -/
theorem publicFiledOnGroup (hg : g.IsSimple) (V : Vision E ξ) (lamp : Bool) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z lamp, Q.MS = A ∧ Vision.StandaloneCorrelation V Z A ∧
      ∀ {n : ℕ} (a : Fin n → YM.Integration.WilsonGraphStandaloneCorrelation.Label g)
        (x : YangMills.Points n) (_hx : x ∈ YangMills.separated n) (k : ℕ),
        Jury.fxt (Measure.outlook Z.scheme Z.criterion (cutoff a)) x k
          (commonCaps (PostedMeasuredCompactCorrelation.leaves (R:=R) (fun i => (a i).1)
            (fun i => (a i).2)) (within a)) =
          converted (PostedAppointedConversion.filed Z Q.MS Q.matching (Teller.logNu 1)) k a x := by
  dsimp only
  obtain ⟨Q, hQ, hV, paid⟩ := separatedGraphSumOnGroupFiledDatum (R:=R) hg V lamp
  refine ⟨Q, hQ, hV, ?_⟩
  intro n a x hx k
  have actual : AllAppointedGraphSums R (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)
      Q.MS (Teller.logNu 1) := by
    rw [hQ]
    exact paid
  exact publicFiledAt _ Q.MS Q.matching actual a ⟨x, hx⟩ k

end YM.Answer.ContinuumLimit
end
