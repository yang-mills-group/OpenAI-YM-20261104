import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentGroupFirstWardTree
import YM.Integration.WilsonGraphPublishedShapeEstimate
import YM.Integration.WilsonGraphDirectPaperCorrelation
import YM.Integration.WilsonGraphGroupPositionReference
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.StandaloneCorrelation

set_option autoImplicit false
noncomputable section
universe u

namespace YM.Integration.WilsonGraphGraphPaperCorrelations

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

theorem modelData (g : YangMills.GaugeGroup) :
    _root_.IssuedMaxwell.GraphCoefficients.issued g =
      ⟨_root_.IssuedMaxwell.GraphCorrelation.read g, _root_.IssuedMaxwell.GraphReader.name g⟩ := rfl

theorem graphRead (g : YangMills.GaugeGroup) :
    WilsonGraphFiledPaperCorrelations.GroupBareRead g (_root_.IssuedMaxwell.GraphCoefficients.issued g) :=
  fun {n} k a x hx => WilsonGraphGroupPositionReference.agreement g n k a x hx

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
    FiledCorrelations (_root_.IssuedMaxwell.GraphCoefficients.issued g) S Hₘ ∧
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
    (paid : WilsonGraphDirectPaperCorrelation.AtPeriods hg E pick Q) : AtPeriods hg E pick Q := by
  obtain ⟨regular, trajectory, original, Fper, fixed, rows⟩ := paid
  refine ⟨regular, trajectory, original, Fper, fixed, ?_⟩
  intro p hp
  obtain ⟨period, strict, ultraviolet, ordered, adjoint, converges, phases,
    standalone, signed, measured, buyers, observations⟩ := rows p hp
  exact ⟨period, strict, ultraviolet, ordered, adjoint, converges, phases,
    standalone, signed, measured, buyers,
    buyers (_root_.IssuedMaxwell.GraphCoefficients.issued g) (graphRead g), observations⟩

theorem finiteAndSmearedOnPick (hg : g.IsSimple)
    (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (paid : AtPeriods hg E pick Q) (p : ℕ → ℕ) (hp : StrictMono p)
    (b : ℕ) {ι : Type} (l : Filter ι) (r : ι → ℝ) (approaches : Tendsto r l trail)
    {n d : ℕ} (U : Set (Points n)) (B : Roi U) {α : Type} (t : Taster α)
    (u : α → ι → Tags g.core d n)
    (salaries : ∀ i : α, ∀ k : Fin n, SeatsW.Salary ℂ l 1 (fun j => u i j k))
    (a : Bool) :
    LinePrices (pick (ElectedPublication.order p hp))
      (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) l r t U u a b := by
  obtain ⟨_, _, _, _, _, rows⟩ := paid
  obtain ⟨_, _, _, _, _, _, _, standalone, _, _, _, _, _⟩ := rows p hp
  exact standalone.finiteAndSmeared b l r approaches U B t u salaries a

open scoped Topology

theorem graphGround (g : YangMills.GaugeGroup) {n : ℕ}
    (S : YangMills.Matching.Conversion (YangMills.maxwellReference g))
    (a : Fin n → YangMills.Matching.Label (YangMills.maxwellReference g))
    (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) :
    S.correlation (_root_.IssuedMaxwell.GraphCoefficients.issued g) 0 a x =
      (YangMills.maxwellReference g).moment x (fun i => (a i).2.val) :=
  _root_.PhysicalMatching.H7IndependentGroupFirstWardTree.groupLeading S a x hx

theorem graphGroundGerm (g : YangMills.GaugeGroup) {n : ℕ}
    (S : YangMills.Matching.Conversion (YangMills.maxwellReference g))
    (a : Fin n → YangMills.Matching.Label (YangMills.maxwellReference g))
    (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) :
    (fun y => S.correlation (_root_.IssuedMaxwell.GraphCoefficients.issued g) 0 a y)
      =ᶠ[𝓝 x] fun y => (YangMills.maxwellReference g).moment y (fun i => (a i).2.val) := by
  filter_upwards [(YangMills.separated n).isOpen.mem_nhds hx] with y hy
  exact graphGround g S a y hy

theorem maxwellJetAt (g : YangMills.GaugeGroup) {n j : ℕ}
    (S : YangMills.Matching.Conversion (YangMills.maxwellReference g))
    (a : Fin n → YangMills.Matching.Label (YangMills.maxwellReference g))
    (x : YangMills.Points n) (hx : x ∈ YangMills.separated n)
    (field : YangMills.Points n → ℂ) {C : ℝ}
    (price : YangMills.Matching.shapeJetEstimateAt j field
      (fun y => S.correlation (_root_.IssuedMaxwell.GraphCoefficients.issued g) 0 a y) x C) :
    YangMills.Matching.shapeJetEstimateAt j field
      (fun y => (YangMills.maxwellReference g).moment y (fun i => (a i).2.val)) x C :=
  _root_.YM.Integration.WilsonGraphPublishedShapeEstimate.jetTransport
    Filter.EventuallyEq.rfl (graphGroundGerm g S a x hx) price

theorem maxwellAndAllOrdersOnPick (hg : g.IsSimple)
    (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (paid : AtPeriods hg E pick Q) (p : ℕ → ℕ) (hp : StrictMono p) :
    let V := pick (ElectedPublication.order p hp)
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let S := _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching
      (_root_.YM.FVA2.Teller.logNu 1)
    let m := _root_.YM.Answer.ContinuumLimit.ElectedMeasurement.publicMeasurement hg V Z Q
    YangMills.Matching.CorrelationOnly.FiledCorrelations
        (_root_.IssuedMaxwell.GraphCoefficients.issued g) S m ∧
      ∀ {n : ℕ} (a : Fin n → YangMills.Matching.Label (YangMills.maxwellReference g))
        (x : YangMills.Points n), x ∈ YangMills.separated n →
        S.correlation (_root_.IssuedMaxwell.GraphCoefficients.issued g) 0 a x =
          (YangMills.maxwellReference g).moment x (fun i => (a i).2.val) := by
  obtain ⟨_, _, _, _, _, rows⟩ := paid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, group, _⟩ := rows p hp
  refine ⟨group, ?_⟩
  intro n a x hx
  exact graphGround g _ a x hx

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

theorem fromPaper (hg : g.IsSimple)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (a : YM.Axis) {ε : ℝ} (O : YM.Integration.Election.OrderS g.core)
    (paid : WilsonGraphDirectPaperCorrelation.Paper.{u} hg H ε a O Q) : Paper.{u} hg H ε a O Q := by
  obtain ⟨E, bills, budget, row, fixed, clusters, admitted⟩ := paid
  refine ⟨E, bills, budget, row, fixed, clusters, ?_⟩
  intro cohort issued
  obtain ⟨pick, retained, reads, comparisons, receipts, shapes, periods⟩ := admitted cohort issued
  exact ⟨pick, retained, reads, comparisons, receipts, shapes, atPeriods hg E pick Q periods⟩

theorem onPaper (hg : g.IsSimple)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (nominated : Q.MS = YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core)
    (a : YM.Axis) {ε : ℝ} (positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core) :
    Paper.{u} hg H ε a O Q :=
  fromPaper hg Q a O (WilsonGraphDirectPaperCorrelation.onPaper.{u} hg Q nominated a positive O)

theorem beforeConstruction (hg : g.IsSimple) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = A ∧
      ∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core),
        Paper.{u} hg H ε a O Q  := by
  dsimp only
  obtain ⟨Q, nominated, elected⟩ := WilsonGraphDirectPaperCorrelation.beforeConstruction.{u} (H := H) hg
  refine ⟨Q, nominated, ?_⟩
  intro a ε positive O
  exact fromPaper hg Q a O (elected a positive O)

theorem groupPublication (g : YangMills.GaugeGroup) (hg : g.IsSimple) :
    let H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = A ∧
      Paper.{u} hg H 1 YM.timeAxis (_root_.IssuedBridge.PostedGroupCalendar.schedule g) Q  := by
  dsimp only
  obtain ⟨Q, nominated, paid⟩ := WilsonGraphDirectPaperCorrelation.groupPublication.{u} g hg
  exact ⟨Q, nominated, fromPaper hg Q YM.timeAxis (_root_.IssuedBridge.PostedGroupCalendar.schedule g) paid⟩

end YM.Integration.WilsonGraphGraphPaperCorrelations

