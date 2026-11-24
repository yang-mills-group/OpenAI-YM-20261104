import YM.Integration.WilsonGraphPublishedShapeEstimate
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedConversion
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PreElectedMeasuredPublication
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PreElectedPublication
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.OriginalStageCostPublication

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonGraphPreElectedShapeEstimates
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

def Elected (hg : g.IsSimple) (H : g.core.Simple) (ε : ℝ) (a : YM.Axis)
    (O : YM.Integration.Election.OrderS g.core) (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) : Prop :=
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
  ∃ E : YM.Answer.ContinuumLimit.Construction.{u} H ε a O, PhysicalMatching.H7OriginalWeakBookBudget.prediction c E.paths.kit ∧
    ∃ row : Row E, Fixed E row ∧ Clusters E row ∧
    ∀ (cohort : Ultrafilter (ℕ × ℕ) → Prop)
      (_issued : ∀ (ξ : YM.Extraction.Order) (l : Ultrafilter (ℕ × ℕ)),
        (l : Filter (ℕ × ℕ)) ≤ ξ.fuse → cohort l),
    ∃ pick : (ξ : YM.Extraction.Order) → Vision E ξ,
      (∀ ξ, Retained E cohort ξ (pick ξ)) ∧ (∀ ξ, Reads E row (pick ξ)) ∧
      (∀ (ξ : YM.Extraction.Order) (lamp : Bool), ∃ oldQ : Perspective H Z lamp, oldQ.MS = A ∧
        _root_.IssuedBridge.PostedAppointedConversion.filed Z oldQ.MS oldQ.matching (YM.FVA2.Teller.logNu 1) =
          _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching (YM.FVA2.Teller.logNu 1) ∧
        Vision.StandaloneCorrelation (pick ξ) Z A ∧ SourceOnlyGraphSum.EveryCoefficient Z A
          (YM.FVA2.Teller.logNu 1)) ∧ Receipts hg E pick ∧
      (∀ ξ, Vision.StandaloneCorrelation (pick ξ) Z A ∧ ReferenceShape Z (pick ξ) Q ∧
        CompactReference Z (pick ξ) Q ∧ TestedReference Z (pick ξ) Q)

def StageElected (hg : g.IsSimple) (H : g.core.Simple) (ε : ℝ) (a : YM.Axis)
    (O : YM.Integration.Election.OrderS g.core) (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) : Prop :=
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
  ∃ E : YM.Answer.ContinuumLimit.Construction.{u} H ε a O, StageTariff.ActualBills c E.paths ∧ PhysicalMatching.H7OriginalWeakBookBudget.prediction c E.paths.kit ∧
    ∃ row : Row E, Fixed E row ∧ Clusters E row ∧
    ∀ (cohort : Ultrafilter (ℕ × ℕ) → Prop)
      (_issued : ∀ (ξ : YM.Extraction.Order) (l : Ultrafilter (ℕ × ℕ)),
        (l : Filter (ℕ × ℕ)) ≤ ξ.fuse → cohort l),
    ∃ pick : (ξ : YM.Extraction.Order) → Vision E ξ,
      (∀ ξ, Retained E cohort ξ (pick ξ)) ∧ (∀ ξ, Reads E row (pick ξ)) ∧
      (∀ (ξ : YM.Extraction.Order) (lamp : Bool), ∃ oldQ : Perspective H Z lamp, oldQ.MS = A ∧
        _root_.IssuedBridge.PostedAppointedConversion.filed Z oldQ.MS oldQ.matching (YM.FVA2.Teller.logNu 1) =
          _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching (YM.FVA2.Teller.logNu 1) ∧
        Vision.StandaloneCorrelation (pick ξ) Z A ∧ SourceOnlyGraphSum.EveryCoefficient Z A
          (YM.FVA2.Teller.logNu 1) ∧
        (cT Z < 0 ∧ ∀ r : ℝ, cT Z * (pick ξ).T Z r = (Signal (pick ξ) Z r).re) ∧
        MeasuredMixedCompact (pick ξ) Z oldQ.MS oldQ.matching) ∧ Receipts hg E pick ∧
      (∀ ξ, Vision.StandaloneCorrelation (pick ξ) Z A ∧ ReferenceShape Z (pick ξ) Q ∧
        CompactReference Z (pick ξ) Q ∧ TestedReference Z (pick ξ) Q)

def MeasuredElected (hg : g.IsSimple) (H : g.core.Simple) (ε : ℝ) (a : YM.Axis)
    (O : YM.Integration.Election.OrderS g.core) (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) : Prop :=
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
  ∃ E : YM.Answer.ContinuumLimit.Construction.{u} H ε a O, PhysicalMatching.H7OriginalWeakBookBudget.prediction c E.paths.kit ∧
    ∃ row : Row E, Fixed E row ∧ Clusters E row ∧
    ∀ (cohort : Ultrafilter (ℕ × ℕ) → Prop)
      (_issued : ∀ (ξ : YM.Extraction.Order) (l : Ultrafilter (ℕ × ℕ)),
        (l : Filter (ℕ × ℕ)) ≤ ξ.fuse → cohort l),
    ∃ pick : (ξ : YM.Extraction.Order) → Vision E ξ,
      (∀ ξ, Retained E cohort ξ (pick ξ)) ∧ (∀ ξ, Reads E row (pick ξ)) ∧
      (∀ (ξ : YM.Extraction.Order) (lamp : Bool), ∃ oldQ : Perspective H Z lamp, oldQ.MS = A ∧
        _root_.IssuedBridge.PostedAppointedConversion.filed Z oldQ.MS oldQ.matching (YM.FVA2.Teller.logNu 1) =
          _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching (YM.FVA2.Teller.logNu 1) ∧
        Vision.StandaloneCorrelation (pick ξ) Z A ∧ SourceOnlyGraphSum.EveryCoefficient Z A
          (YM.FVA2.Teller.logNu 1) ∧
        (cT Z < 0 ∧ ∀ r : ℝ, cT Z * (pick ξ).T Z r = (Signal (pick ξ) Z r).re) ∧
        MeasuredMixedCompact (pick ξ) Z oldQ.MS oldQ.matching) ∧ Receipts hg E pick ∧
      (∀ ξ, Vision.StandaloneCorrelation (pick ξ) Z A ∧ ReferenceShape Z (pick ξ) Q ∧
        CompactReference Z (pick ξ) Q ∧ TestedReference Z (pick ξ) Q)

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

theorem filedDatum (Z : WilsonPrescription g.core)
    {raw A : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core))}
    {σ τ : Prescription (Press.portDeck g.core)} {dial lamp : Bool}
    (first : Main.Match Z H raw σ dial) (second : Main.Match Z H A τ lamp)
    (same : raw = A) (μ : ℝ) :
    _root_.IssuedBridge.PostedAppointedConversion.filed Z raw first μ =
      _root_.IssuedBridge.PostedAppointedConversion.filed Z A second μ := by
  subst A
  rfl

theorem sameFiled (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    {lamp : Bool} (oldQ : Perspective H Z lamp) (same : oldQ.MS = Q.MS) (μ : ℝ) :
    _root_.IssuedBridge.PostedAppointedConversion.filed Z oldQ.MS oldQ.matching μ =
      _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching μ :=
  filedDatum Z oldQ.matching Q.matching same μ

theorem original (hg : g.IsSimple) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = A ∧
      (∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core)
        (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core), Elected.{u} hg H ε a O c Q) ∧
      (∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core)
        (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core), MeasuredElected.{u} hg H ε a O c Q) ∧
      (∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core),
        StageElected.{u} hg H ε a O (StageTariff.costs (StageTariff.base g.core)) Q) := by
  dsimp only
  obtain ⟨Q, nominated, onField⟩ := WilsonGraphPublishedShapeEstimate.beforeConstruction.{u} (H := H) hg
  refine ⟨Q,nominated,?_,?_,?_⟩
  · intro a ε positive O c
    obtain ⟨E,budget,row,fixed,clusters,admitted⟩ :=
      YM.Answer.ContinuumLimit.PreElectedPublication.original.{u} hg a H positive O c
    refine ⟨E,budget,row,fixed,clusters,?_⟩
    intro cohort issued
    obtain ⟨pick,retained,reads,comparisons,receipts⟩ := admitted cohort issued
    refine ⟨pick,retained,reads,?_,receipts,fun ξ => onField E.paths E (pick ξ)⟩
    intro ξ lamp
    obtain ⟨oldQ,appointed,paidRow⟩ := comparisons ξ lamp
    exact ⟨oldQ,appointed,sameFiled _ Q oldQ (appointed.trans nominated.symm) (YM.FVA2.Teller.logNu 1),paidRow⟩
  · intro a ε positive O c
    obtain ⟨E,budget,row,fixed,clusters,admitted⟩ :=
      YM.Answer.ContinuumLimit.PreElectedPublication.measuredOriginal.{u} hg a H positive O c
    refine ⟨E,budget,row,fixed,clusters,?_⟩
    intro cohort issued
    obtain ⟨pick,retained,reads,comparisons,receipts⟩ := admitted cohort issued
    refine ⟨pick,retained,reads,?_,receipts,fun ξ => onField E.paths E (pick ξ)⟩
    intro ξ lamp
    obtain ⟨oldQ,appointed,paidRow⟩ := comparisons ξ lamp
    exact ⟨oldQ,appointed,sameFiled _ Q oldQ (appointed.trans nominated.symm) (YM.FVA2.Teller.logNu 1),paidRow⟩
  · intro a ε positive O
    obtain ⟨E,bills,budget,row,fixed,clusters,admitted⟩ :=
      YM.Answer.ContinuumLimit.PreElectedPublication.stageOriginal.{u} hg a H positive O
    refine ⟨E,bills,budget,row,fixed,clusters,?_⟩
    intro cohort issued
    obtain ⟨pick,retained,reads,comparisons,receipts⟩ := admitted cohort issued
    refine ⟨pick,retained,reads,?_,receipts,fun ξ => onField E.paths E (pick ξ)⟩
    intro ξ lamp
    obtain ⟨oldQ,appointed,paidRow⟩ := comparisons ξ lamp
    exact ⟨oldQ,appointed,sameFiled _ Q oldQ (appointed.trans nominated.symm) (YM.FVA2.Teller.logNu 1),paidRow⟩

theorem publicHierarchy (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ) (p : ℕ → ℕ) (hp : StrictMono p) :
    ((YM.Answer.ContinuumLimit.PreElectedPublication.publication E pick).refine p hp).hierarchy =
      YangMills.hierarchy (pick (ElectedPublication.order p hp)).pupil.last
        (pick (ElectedPublication.order p hp)).pupil.P := rfl
end YM.Integration.WilsonGraphPreElectedShapeEstimates
end
