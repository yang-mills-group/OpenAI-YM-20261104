import YM.Integration.WilsonGraphFiledPaperCorrelationCore
import YM.Integration.WilsonGraphFixedRadiusReturns
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.StageTemplateTariff

set_option autoImplicit false
noncomputable section
universe u

namespace YM.Integration.WilsonGraphDirectPaperCorrelation

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



open YangMills.Matching.CorrelationOnly

variable {E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O} {ξ : YM.Extraction.Order}

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open scoped Topology BigOperators Classical ContDiff
open FVA2.GradedFar FVA2.Dframe
open YangMills YangMills.Wilson YangMills.Matching
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


def AtPeriods (hg : g.IsSimple) (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) : Prop :=
  let B := YangMills.maxwellReference g
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := WilsonCapturedPhysicalMSDatum.original g.core
  let S := _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching
      (YM.FVA2.Teller.logNu 1)
  let run := YM.Answer.ContinuumLimit.PreElectedPublication.publication E pick
  let D := _root_.IssuedRuns.FinalWilsonData.original E.paths.family E.paths.makes hg B
  WilsonRegularity run.family ∧ WilsonTrajectory B run.family ∧
  run.originalPointReturns ∧
  ∃ Fper : PeriodPointTable run.family, FixedPointReturns run.family Fper ∧
    ∀ (p : ℕ → ℕ) (hp : StrictMono p),
    let V := pick (ElectedPublication.order p hp)
    let chosen := run.refine p hp
    let Hₘ := ElectedMeasurement.publicMeasurement hg V Z Q
    V.pupil.f.per.choose = p ∘ chosen.indices ∧ StrictMono chosen.indices ∧
    YM.FullVolume.PositionsUV E.paths.family YM.Extraction.Sequence.full ∧
    (⟨.full, V.pupil.f.per⟩ : YM.Extraction.Order).Ordered E.paths.family V.pupil.S ∧
    D.AdjointOn chosen.hierarchy ∧
    run.family.Converges (p ∘ chosen.indices)
      (fun v => chosen.hierarchy.correlation none (chosen.hierarchy.project ∘ v)) ∧
    ObservablePhases.Law D chosen.hierarchy ∧
    Vision.StandaloneCorrelation V Z A ∧
    (cT Z < 0 ∧ ∀ r : ℝ, cT Z * V.T Z r = (Signal V Z r).re) ∧
    MeasuredMixedCompact V Z Q.MS Q.matching ∧
    (∀ M : YangMills.MSbar.Coefficients B, WilsonGraphFiledPaperCorrelations.GroupBareRead g M →
      FiledCorrelations M S Hₘ) ∧
    ∀ (r : ℝ) (n : ℕ) (d : Fin n → ℕ)
        (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i)),
      let w := WilsonGraphFixedRadiusReturns.tokens V Z r d v
      let a := Hₘ.inputs r (publicLetters d v)
      WilsonGraphFixedRadiusReturns.Observed Fper chosen.hierarchy (p ∘ chosen.indices) w a ∧
      ∀ L : TestTable run.family, HasTestLimits run.family p L →
        ∀ t : YangMills.SeparatedTest n,
          L n w t = ∫ x, t x * chosen.hierarchy.correlation none a x


theorem atPeriods (hg : g.IsSimple) (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (nominated : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core)
    (receipts : YM.Answer.ContinuumLimit.PreElectedPublication.Receipts hg E pick) : AtPeriods hg E pick Q := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let run := YM.Answer.ContinuumLimit.PreElectedPublication.publication E pick
  obtain ⟨regular, trajectory, ⟨Fper, fixed, outer⟩, returns⟩ := receipts
  refine ⟨regular, trajectory, ⟨Fper, fixed, outer⟩, Fper, fixed, ?_⟩
  intro p hp
  let V := pick (ElectedPublication.order p hp)
  let chosen := run.refine p hp
  obtain ⟨period, strict, ultraviolet, ordered, adjoint, converges, phase, earlier⟩ := returns p hp
  obtain ⟨_, _, full, _⟩ := earlier true
  have onDatum : Vision.StandaloneCorrelation V Z Q.MS := by
    rw [nominated]
    exact full
  obtain ⟨signed, measured⟩ := publicMeasuredOnPerspective V Z Q onDatum
  have reference := WilsonGraphFiledPaperCorrelations.atBareVision hg V Q nominated
  refine ⟨period, strict, ultraviolet, ordered, adjoint, converges, phase,
    full, signed, measured, ?_, ?_⟩
  · intro M read
    exact WilsonGraphFiledPaperCorrelations.referenceToModel read reference
  · intro r n d v
    let w := WilsonGraphFixedRadiusReturns.tokens V Z r d v
    let a := (ElectedMeasurement.publicMeasurement hg V Z Q).inputs r (publicLetters d v)
    have sectionEq : chosen.hierarchy.project ∘ w = a := by
      change chosen.hierarchy.project ∘ WilsonGraphFixedRadiusReturns.tokens V Z r d v =
        (ElectedMeasurement.publicMeasurement hg V Z Q).inputs r (publicLetters d v)
      rw [ElectedMeasurement.publicInputs]
      exact WilsonGraphFixedRadiusReturns.projected V Z r d v
    exact ⟨WilsonGraphFixedRadiusReturns.observed Fper fixed chosen.hierarchy
        (p ∘ chosen.indices) w a sectionEq (outer p hp n w) converges,
      fun L pre t => WilsonGraphFixedRadiusReturns.represented chosen.hierarchy strict
        w a sectionEq L pre converges t⟩

def Paper (hg : g.IsSimple) (H : g.core.Simple) (ε : ℝ) (a : YM.Axis)
    (O : YM.Integration.Election.OrderS g.core)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) : Prop :=
  let c := StageTariff.paperCosts g.core
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
        CompactReference Z (pick ξ) Q ∧ TestedReference Z (pick ξ) Q) ∧ AtPeriods hg E pick Q

theorem onPaper (hg : g.IsSimple)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (nominated : Q.MS = YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core)
    (a : YM.Axis) {ε : ℝ} (positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core) :
    Paper.{u} hg H ε a O Q := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨E,bills,budget,row,fixed,clusters,admitted⟩ :=
    YM.Answer.ContinuumLimit.PreElectedPublication.originalPaper.{u} hg a H positive O
  refine ⟨E,bills,budget,row,fixed,clusters,?_⟩
  intro cohort issued
  obtain ⟨pick,retained,reads,comparisons,receipts⟩ := admitted cohort issued
  refine ⟨pick,retained,reads,?_,receipts,?_,atPeriods hg E pick Q nominated receipts⟩
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

theorem beforeConstruction (hg : g.IsSimple) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = A ∧
      ∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core),
        Paper.{u} hg H ε a O Q := by
  dsimp only
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := WilsonCapturedPhysicalMSDatum.original g.core
  obtain ⟨Q, nominated⟩ := YM.Answer.ContinuumLimit.compared H Z true A
  refine ⟨Q, nominated, ?_⟩
  intro a ε positive O
  exact onPaper.{u} hg Q nominated a positive O

theorem groupPublication (g : YangMills.GaugeGroup) (hg : g.IsSimple) :
    let H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = A ∧
      Paper.{u} hg H 1 YM.timeAxis (_root_.IssuedBridge.PostedGroupCalendar.schedule g) Q := by
  dsimp only
  obtain ⟨Q,hnominated,all⟩ :=
    beforeConstruction.{u} (H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg) hg
  exact ⟨Q,hnominated,all YM.timeAxis zero_lt_one (_root_.IssuedBridge.PostedGroupCalendar.schedule g)⟩

end YM.Integration.WilsonGraphDirectPaperCorrelation

