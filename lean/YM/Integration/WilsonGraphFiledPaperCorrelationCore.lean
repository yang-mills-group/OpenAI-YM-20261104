import YM.Integration.WilsonGraphSeparatedFiledEstimates
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PreElectedPublication
import YM.Integration.WilsonGraphPublishedShapeEstimate
import YM.Integration.WilsonGraphConstructedMeasuredCompactCorrelation
import YM.Integration.WilsonGraphAppointedMeasurementLaws

set_option autoImplicit false
noncomputable section
universe u



namespace YM.Integration.WilsonGraphFiledPaperCorrelations
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

theorem atVision (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (_nominated : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core)
    (M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g))
    (read : M.correlation = WilsonGraphStandaloneCorrelation.bare g) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let S := _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching
      (YM.FVA2.Teller.logNu 1)
    FiledCorrelations M S (ElectedMeasurement.publicMeasurement hg V Z Q) := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let Hₘ := ElectedMeasurement.publicMeasurement hg V Z Q
  apply groupFiledCorrelationsOfShape
  intro n p j d K compact separated
  have paid : YM.Answer.ContinuumLimit.AllAppointedGraphSums E.paths Z Q.MS (YM.FVA2.Teller.logNu 1) :=
    (SourceOnlyGraphSum.originalAgreement (R := E.paths) Z Q.MS
    (YM.FVA2.Teller.logNu 1)).mpr
    (SourceOnlyGraphSum.atMatch Z Q.MS Q.matching (YM.FVA2.Teller.logNu 1))
  exact WilsonGraphPublishedShapeEstimate.onField (R := E.paths) (Z := Z) (V := V) (Q := Q)
    paid Hₘ (Filter.Eventually.of_forall fun _ => rfl) M read n p j d K compact separated (by
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with s hs
      intro phase v o y hy
      exact ElectedMeasurement.scalar V Z phase d v hs o y hy)

def bareModel (g : YangMills.GaugeGroup) :
    YangMills.MSbar.Coefficients (YangMills.maxwellReference g) :=
  ⟨WilsonGraphStandaloneCorrelation.bare g, 0⟩

theorem atBareVision (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (nominated : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let S := _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching
      (YM.FVA2.Teller.logNu 1)
    FiledCorrelations (bareModel g) S (ElectedMeasurement.publicMeasurement hg V Z Q) :=
  atVision hg V Q nominated (bareModel g) rfl

def GroupBareRead (g : YangMills.GaugeGroup)
    (M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g)) : Prop :=
  ∀ {n : ℕ} (k : ℕ) (v : Fin n → Label (YangMills.maxwellReference g))
    (x : YangMills.Points n), x ∈ YangMills.separated n →
      M.correlation n k v x = WilsonGraphStandaloneCorrelation.bare g n k v x

theorem inheritGroupBareRead
    {M N : YangMills.MSbar.Coefficients (YangMills.maxwellReference g)}
    (read : GroupBareRead g N) (same : M.correlation = N.correlation) : GroupBareRead g M := by
  intro n k v x hx
  rw [same]
  exact read k v x hx

theorem referenceToModel {C : YangMills.WilsonFamily g} {T : YangMills.Hierarchy C}
    {S : YangMills.Matching.Conversion (YangMills.maxwellReference g)}
    {HM : YangMills.Matching.CorrelationOnly.Measurement (YangMills.maxwellReference g) T}
    {M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g)}
    (read : GroupBareRead g M) (priced : FiledCorrelations (bareModel g) S HM) :
    FiledCorrelations M S HM := by
  refine filedCorrelationsOnSeparated S HM ?_ priced
  intro n k v x hx
  exact (read k v x hx).symm

theorem atSeparatedVision (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (nominated : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core)
    (M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g))
    (read : GroupBareRead g M) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let S := _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching
      (YM.FVA2.Teller.logNu 1)
    FiledCorrelations M S (ElectedMeasurement.publicMeasurement hg V Z Q) := by
  exact referenceToModel read (atBareVision hg V Q nominated)

def OnRun (hg : g.IsSimple) (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
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
  run.originalPointReturns ∧ ∀ (p : ℕ → ℕ) (hp : StrictMono p),
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
    ∀ M : YangMills.MSbar.Coefficients B, M.correlation = WilsonGraphStandaloneCorrelation.bare g →
      FiledCorrelations M S Hₘ

theorem onRun (hg : g.IsSimple) (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (nominated : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core)
    (receipts : YM.Answer.ContinuumLimit.PreElectedPublication.Receipts hg E pick) : OnRun hg E pick Q := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨regular,trajectory,points,returns⟩ := receipts
  refine ⟨regular,trajectory,points,?_⟩
  intro p hp
  let V := pick (ElectedPublication.order p hp)
  obtain ⟨period,strict,ultraviolet,ordered,adjoint,converges,phase,earlier⟩ := returns p hp
  obtain ⟨_,_,full,_⟩ := earlier true
  have onDatum : Vision.StandaloneCorrelation V Z Q.MS := by
    rw [nominated]
    exact full
  obtain ⟨signed,measured⟩ := publicMeasuredOnPerspective V Z Q onDatum
  exact ⟨period,strict,ultraviolet,ordered,adjoint,converges,phase,full,signed,measured,
    fun M read => atVision hg V Q nominated M read⟩


end YM.Integration.WilsonGraphFiledPaperCorrelations

