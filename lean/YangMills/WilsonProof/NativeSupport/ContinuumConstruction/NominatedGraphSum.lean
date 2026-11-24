import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.StandaloneCorrelation
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFieldCorrelation
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YM.MS.Graphical.CommonGates
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

/-- The bare graph screen at the single common grade, with one filed field conversion at
each insertion's own grade and one signed coupling conversion. -/
def AppointedGraphSum (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
    (μ : ℝ) {n h : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (within : ∀ i, d i ≤ h) (x : Stage n) (k : ℕ) : ℂ :=
  ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
    if (∑ i, (ν i).val) ≤ k then
      (couplingPower (PostedRealFiledCoupling.coefficient Z A μ) j.val (k-∑ i,(ν i).val) : ℂ) *
      YM.MS.Graphical.separatedGraphSum μ g.core h x.val j.val (fun i => XSpace.Normalize.up (within i)
        ((PowerSeries.coeff (ν i).val (Measure.Z Z.scheme Z.criterion μ A (d i))) (v i))) else 0

def AllAppointedGraphSums (R : Run g.core) (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core))) (μ : ℝ) : Prop :=
  ∀ {n h : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (within : ∀ i,d i ≤ h) (x : Stage n) (k : ℕ),
    Jury.fxt (Measure.outlook Z.scheme Z.criterion h) x.val k
      (commonCaps (PostedMeasuredCompactCorrelation.leaves (R:=R) d v) within) =
        AppointedGraphSum Z A μ d v within x k

theorem separatedGraphSumOnNominatedVision (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core))) (lamp : Bool) :
    ∃ Q : Perspective H Z lamp, Q.MS=A ∧ Vision.StandaloneCorrelation V Z A ∧
      ∀ μ : ℝ, AllAppointedGraphSums R Z A μ := by
  obtain ⟨Q,hQ⟩ := compared H Z lamp A
  refine ⟨Q,hQ,hQ ▸ Vision.standaloneFromActualField V Q,?_⟩
  intro μ n h d v within x k
  have matched := Q.matching
  rw [hQ] at matched
  have physical := PostedAppointedFieldCorrelation.original (R:=R) Z A matched μ d v within x k
  have bare (j : ℕ) : YM.MS.Graphical.separatedGraphSum μ g.core h x.val j = Equator.wave μ A h n x j :=
    YM.MS.Graphical.identification_screen μ A x.property
  simpa only [AppointedGraphSum, bare] using physical

theorem separatedGraphSumOnGroupFiledDatum (hg : g.IsSimple) (V : Vision E ξ) (lamp : Bool) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z lamp, Q.MS=A ∧ Vision.StandaloneCorrelation V Z A ∧
      AllAppointedGraphSums R Z A (Teller.logNu 1) := by
  dsimp only
  obtain ⟨Q, hQ, hV, hs⟩ := separatedGraphSumOnNominatedVision (R:=R) V
    (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonCapturedPhysicalMSDatum.original g.core) lamp
  exact ⟨Q, hQ, hV, hs _⟩
end YM.Answer.ContinuumLimit
