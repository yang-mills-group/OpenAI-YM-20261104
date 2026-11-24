import YM.Integration.WilsonGraphPaperElectedShapeEstimates
import YM.Integration.WilsonGraphGroupPositionReference
import YM.Integration.WilsonGraphAppointedMeasurementLaws
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneMeasuredCorrelationEstimates

set_option autoImplicit false
noncomputable section
universe u

namespace YangMills.Matching.CorrelationOnly

open Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g} {T : Hierarchy C}

/-- The compact, spatial derivative and tested correlation estimates on one public field. -/
structure PublishedCorrelations (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) : Prop where
  jets : ShapeIncome M S H
  compact (n p : ℕ) (d : Fin n → ℕ) (o : Spacetime) (K : Set (Points n))
      (_compact : IsCompact K) (_separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ phase : Option T.Character,
      ∀ (v : (i : Fin n) → B.sector (d i)) (x : Points n), x ∈ K →
      ‖correlationError M S H p (fun i => ⟨d i, v i⟩) phase o s x‖ ≤
        A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1)
  tested (n : ℕ) (d : Fin n → ℕ) (phase : Option T.Character)
      (v : (i : Fin n) → B.sector (d i)) (o : Spacetime) :
    let a : Fin n → Label B := fun i => ⟨d i,v i⟩
    HasExpansion 0 H.clock (fun s x => T.correlation phase (H.inputs s a)
      (WithLp.toLp 2 fun i => o + s • x i)) (fun k x => S.correlation M k a x)

theorem correlationsOfShape (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) (shapes : ShapeIncome M S H) : PublishedCorrelations M S H where
  jets := shapes
  compact n p d o K hK separated := by
    obtain ⟨A,hA,late⟩ := shapes n p 0 d K hK separated
    exact ⟨A,hA,late.mono fun s hs phase v x hx => shapeValue (hs phase v o x hx)⟩
  tested n d phase v o := by
    apply testedOfShapeJets H.positive (clockAtZero H)
    intro p K hK separated
    obtain ⟨A,hA,late⟩ := shapes n p 0 d K hK separated
    refine ⟨A * (∏ i, sectorMass (v i)),
      mul_nonneg hA (Finset.prod_nonneg fun i _ => sectorMass_nonneg (v i)), ?_⟩
    exact late.mono fun s hs x hx => hs phase v o x hx

theorem correlationsWithWard (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) (paid : PublishedCorrelations M S H) (phases : PhaseProximity H)
    (independent : ∃! P : WardStress.Series B, WardStress.Determined M S P)
    (named : ∀ P : WardStress.Series B, WardStress.Determined M S P → namedStress H P) :
    Estimates M S H :=
  measuredEstimates M S H paid.jets phases independent named

end YangMills.Matching.CorrelationOnly

namespace YM.Integration.WilsonGraphPaperPublishedCorrelation
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


open YangMills.Matching.CorrelationOnly

variable {E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O} {ξ : YM.Extraction.Order}

theorem atVision (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true)
    (nominated : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core)
    (M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g))
    (read : M.correlation = WilsonGraphStandaloneCorrelation.bare g) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let I := WilsonGraphGroupPositionReference.external g hg
    PublishedCorrelations M I.conversion.conversion (ElectedMeasurement.publicMeasurement hg V Z Q) := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let Hₘ := ElectedMeasurement.publicMeasurement hg V Z Q
  apply correlationsOfShape
  rw [WilsonGraphGroupPositionReference.atPerspective hg Q nominated]
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

def OnRun (hg : g.IsSimple) (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) : Prop :=
  let B := YangMills.maxwellReference g
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := WilsonCapturedPhysicalMSDatum.original g.core
  let I := WilsonGraphGroupPositionReference.external g hg
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
      PublishedCorrelations M I.conversion.conversion Hₘ

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
        CompactReference Z (pick ξ) Q ∧ TestedReference Z (pick ξ) Q) ∧ OnRun hg E pick Q

theorem original (hg : g.IsSimple) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let A := WilsonCapturedPhysicalMSDatum.original g.core
    let I := WilsonGraphGroupPositionReference.external g hg
    ∃ Q : Perspective H Z true, Q.MS = A ∧
      I.conversion = _root_.IssuedBridge.PostedPositionConversion.filed Z Q.MS Q.matching
        (YM.FVA2.Teller.logNu 1) ∧
      (∀ M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g),
        M.correlation = WilsonGraphStandaloneCorrelation.bare g →
          (∀ t : YangMills.MSbar.Position.Triangle (YangMills.maxwellReference g),
            t.Admissible → t.RawSlopeAgrees M) ∧ YangMills.MSbar.ConversionValid M I.menu I.conversion) ∧
      ∀ (a : YM.Axis) {ε : ℝ} (_positive : 0 < ε) (O : YM.Integration.Election.OrderS g.core),
        Paper.{u} hg H ε a O Q := by
  dsimp only
  obtain ⟨Q,nominated,_,_,_,paper⟩ :=
    WilsonGraphPaperElectedShapeEstimates.original.{u} (H := H) hg
  refine ⟨Q,nominated,WilsonGraphGroupPositionReference.atPerspective hg Q nominated,?_,?_⟩
  · intro M read
    let I := WilsonGraphGroupPositionReference.external g hg
    exact ⟨I.everyBareSlope M read,I.valid M read⟩
  · intro a ε positive O
    obtain ⟨E,bills,budget,row,fixed,clusters,admitted⟩ := paper a positive O
    refine ⟨E,bills,budget,row,fixed,clusters,?_⟩
    intro cohort issued
    obtain ⟨pick,retained,outer,prior,receipts,prices⟩ := admitted cohort issued
    exact ⟨pick,retained,outer,prior,receipts,prices,onRun hg E pick Q nominated receipts⟩

end YM.Integration.WilsonGraphPaperPublishedCorrelation
end
