import YM.Integration.WilsonGraphPreElectedShapeEstimates
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.StageTemplateTariff

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonGraphPaperElectedShapeEstimates
open Filter Function Set YangMills YangMills.Wilson
open YM YM.Integration YM.Answer.ContinuumLimit YM.Extraction YM.FullVolume
open Climb Lattice Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open Election SignedWilsonExpansion.Museum
open _root_.IssuedBridge.PhysicalPeriodNodes
open scoped Classical Topology

variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : YM.Axis}
  {O : YM.Integration.Election.OrderS g.core}

open YM.Answer.ContinuumLimit.PreElectedPublication YM.Integration.WilsonGraphPublishedShapeEstimate

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
open _root_.IssuedBridge
open YangMills.Matching
open YM.Answer.ContinuumLimit.Vision
open Frames Frames.Cortex Dancer Belfry Belfry.Classroom Belfry.ScaleFits Scale Level GroupS
open SeatsW
open YM.Integration.WilsonGraphStandaloneCorrelation (cutoff within converted)
open YM.Answer.ContinuumLimit.Vision

open YM.Integration.WilsonGraphPreElectedShapeEstimates

theorem paperOn (hg : g.IsSimple)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (nominated : Q.MS = YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core)
    (a : YM.Axis) {ε : ℝ} (positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core) :
    StageElected.{u} hg H ε a O (StageTariff.paperCosts g.core) Q := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨E,bills,budget,row,fixed,clusters,admitted⟩ :=
    YM.Answer.ContinuumLimit.PreElectedPublication.originalPaper.{u} hg a H positive O
  refine ⟨E,bills,budget,row,fixed,clusters,?_⟩
  intro cohort issued
  obtain ⟨pick,retained,reads,comparisons,receipts⟩ := admitted cohort issued
  refine ⟨pick,retained,reads,?_,receipts,?_⟩
  · intro ξ lamp
    obtain ⟨oldQ,appointed,paidRow⟩ := comparisons ξ lamp
    exact ⟨oldQ,appointed,sameFiled Z Q oldQ (appointed.trans nominated.symm)
      (YM.FVA2.Teller.logNu 1),paidRow⟩
  · intro ξ
    let V := pick ξ
    have shapes := referenceCapped (R := E.paths) Z V Q
      (atOneMatch E.paths Z Q (YM.FVA2.Teller.logNu 1))
    have physical := Vision.standaloneFromActualField V Q
    exact ⟨nominated ▸ physical,shapes,referenceCompact Z V Q shapes,referenceTested Z V Q shapes⟩

theorem original (hg : g.IsSimple) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = A ∧
      (∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core)
        (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core), Elected.{u} hg H ε a O c Q) ∧
      (∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core)
        (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core), MeasuredElected.{u} hg H ε a O c Q) ∧
      (∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core),
        StageElected.{u} hg H ε a O (StageTariff.costs (StageTariff.base g.core)) Q) ∧
      (∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core),
        StageElected.{u} hg H ε a O (StageTariff.paperCosts g.core) Q) := by
  dsimp only
  obtain ⟨Q,nominated,generic,measured,base⟩ :=
    WilsonGraphPreElectedShapeEstimates.original.{u} (H := H) hg
  refine ⟨Q,nominated,generic,measured,base,?_⟩
  intro a ε positive O
  exact paperOn.{u} hg Q nominated a positive O

theorem onRefinement (hg : g.IsSimple)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ)
    (paid : let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
      let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
      ∀ ξ, Vision.StandaloneCorrelation (pick ξ) Z A ∧ ReferenceShape Z (pick ξ) Q ∧
        CompactReference Z (pick ξ) Q ∧ TestedReference Z (pick ξ) Q)
    (p : ℕ → ℕ) (hp : StrictMono p) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
    let V := pick (ElectedPublication.order p hp)
    ((YM.Answer.ContinuumLimit.PreElectedPublication.publication E pick).refine p hp).hierarchy =
      YangMills.hierarchy V.pupil.last V.pupil.P ∧
    Vision.StandaloneCorrelation V Z A ∧ ReferenceShape Z V Q ∧
      CompactReference Z V Q ∧ TestedReference Z V Q :=
  ⟨WilsonGraphPreElectedShapeEstimates.publicHierarchy E pick p hp,paid _⟩

end YM.Integration.WilsonGraphPaperElectedShapeEstimates
end
