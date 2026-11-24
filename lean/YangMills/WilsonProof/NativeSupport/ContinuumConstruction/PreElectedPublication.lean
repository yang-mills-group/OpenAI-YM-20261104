import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.ElectedPublicCorrelation
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7JointVisionWeakBookElection
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedElectedMatrixRetainedContinuumLimitVision

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Answer.ContinuumLimit.PreElectedPublication
open Filter Function Set YangMills YangMills.Wilson
open YM YM.Integration YM.Answer.ContinuumLimit YM.Extraction YM.FullVolume
open Climb Lattice Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open Election SignedWilsonExpansion.Museum
open _root_.IssuedBridge.PhysicalPeriodNodes
open scoped Classical Topology

variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : YM.Axis}
  {O : YM.Integration.Election.OrderS g.core}

abbrev Row (E : Construction.{u} H ε e O) :=
  (m n : ℕ) → (Fin n → E.paths.family.book.Token) → YM.Points n → ℂ

def Fixed (E : Construction.{u} H ε e O) (row : Row E) : Prop :=
  FixedPointReturns (YangMills.wilsonFamily E.paths.family) (appoint E.paths.family row)

def Clusters (E : Construction.{u} H ε e O) (row : Row E) : Prop :=
  ∀ (m n : ℕ) (v : Fin n → E.paths.family.book.Token),
    Cluster E.paths.family .full m n (fun N => lifted E.paths.family N m v) (row m n v)

def Retained (E : Construction.{u} H ε e O) (cohort : Ultrafilter (ℕ × ℕ) → Prop)
    (ξ : YM.Extraction.Order) (V : Vision E ξ) : Prop :=
  (V.pupil.Y : Filter (ℕ × ℕ)) ≤ (ξ.refine V.g).fuse ∧ cohort V.pupil.Y ∧
  Log.MatrixTicket (C := E.paths.family) V.pupil.S V.pupil.last.sector.derivatives
    (V.pupil.Y : Filter (ℕ × ℕ)) ∧
  SingleLog V.pupil.last V.pupil.P.port ∧ LogTrace V.pupil.last V.pupil.P.port ∧
  Trace.Target.Result.{u} V.pupil.last H ∧ Trace.Target.Exclusion.{u} V.pupil.last ∧
  V.colours = standT V.pupil.S V.pupil.last.room.kernel.laws V.pupil.last.room.kernel.spin

def Reads (E : Construction.{u} H ε e O) (row : Row E) {ξ : YM.Extraction.Order}
    (V : Vision E ξ) : Prop :=
  ∀ (n : ℕ) (v : Fin n → E.paths.family.book.Token) (K : Set (YM.Points n)),
    IsCompact K → K ⊆ YangMills.WilsonFamily.separated n → ∀ δ : ℝ, 0 < δ →
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
      dist (periodValue (appoint E.paths.family row) (V.pupil.f.per.choose k) v z)
        ((YangMills.hierarchy V.pupil.last V.pupil.P).correlation none
          ((YangMills.hierarchy V.pupil.last V.pupil.P).project ∘ v) z) < δ

def publication (E : Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ) : YangMills.Wilson.Construction g where
  family := YangMills.wilsonFamily E.paths.family
  refine p hp := let V := pick (ElectedPublication.order p hp)
                 ⟨V.g.per.choose, V.g.per.monotone, YangMills.hierarchy V.pupil.last V.pupil.P⟩

theorem reads (E : Construction.{u} H ε e O) (row : Row E) (cluster : Clusters E row)
    {ξ : YM.Extraction.Order} (V : Vision E ξ) : Reads E row V := by
  intro n v K compact inside δ positive
  exact _root_.IssuedBridge.OriginalPointReturns.outer (g := g) H
    V.pupil.last V.pupil.P row cluster n v K compact inside δ positive

theorem points (E : Construction.{u} H ε e O) (row : Row E) (fixed : Fixed E row)
    (cluster : Clusters E row) (pick : (ξ : YM.Extraction.Order) → Vision E ξ) :
    (publication E pick).originalPointReturns := by
  refine ⟨appoint E.paths.family row, fixed, ?_⟩
  intro p hp n v K compact inside δ pos
  let V := pick (ElectedPublication.order p hp)
  have measured := reads E row cluster V n v K compact inside δ pos
  rw [ElectedPublication.period V] at measured
  exact measured

def Receipts (hg : g.IsSimple) (E : Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ) : Prop :=
  let B := YangMills.maxwellReference g
  let run := publication E pick
  let D := _root_.IssuedRuns.FinalWilsonData.original E.paths.family E.paths.makes hg B
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
  WilsonRegularity run.family ∧
  WilsonTrajectory B run.family ∧ run.originalPointReturns ∧
  ∀ (p : ℕ → ℕ) (hp : StrictMono p),
    let V := pick (ElectedPublication.order p hp)
    let chosen := run.refine p hp
    V.pupil.f.per.choose = p ∘ chosen.indices ∧ StrictMono chosen.indices ∧
    YM.FullVolume.PositionsUV E.paths.family YM.Extraction.Sequence.full ∧
    (⟨.full, V.pupil.f.per⟩ : YM.Extraction.Order).Ordered E.paths.family V.pupil.S ∧
    D.AdjointOn chosen.hierarchy ∧
    run.family.Converges (p ∘ chosen.indices)
      (fun v => chosen.hierarchy.correlation none (chosen.hierarchy.project ∘ v)) ∧
    ObservablePhases.Law D chosen.hierarchy ∧
    ∀ lamp : Bool, ∃ Q : Perspective H Z lamp, Q.MS = A ∧
      Vision.StandaloneCorrelation V Z A ∧ SourceOnlyGraphSum.EveryCoefficient Z A (YM.FVA2.Teller.logNu 1)

theorem onConstruction (hg : g.IsSimple) (E : Construction.{u} H ε e O) (row : Row E) (fixed : Fixed E row)
    (cluster : Clusters E row) (pick : (ξ : YM.Extraction.Order) → Vision E ξ) : Receipts hg E pick := by
  let B := YangMills.maxwellReference g
  let D := _root_.IssuedRuns.FinalWilsonData.original E.paths.family E.paths.makes hg B
  refine ⟨D.regular, _root_.IssuedRuns.OriginalTrajectory.original E.paths.family E.paths.makes hg B,
    points E row fixed cluster pick, ?_⟩
  intro p hp
  let V := pick (ElectedPublication.order p hp)
  let Y := YangMills.hierarchy V.pupil.last V.pupil.P
  have limit := YangMills.wilsonLimit V.pupil.last V.pupil.P V.pupil.trackP
  change (YangMills.wilsonFamily E.paths.family).Converges V.pupil.f.per.choose
    (fun v => Y.correlation none (Y.project ∘ v)) at limit
  rw [ElectedPublication.period V] at limit
  exact ⟨ElectedPublication.period V, V.g.per.monotone, V.pupil.TrackU, V.pupil.trackP,
    _root_.IssuedBridge.OriginalQuotient.original E.paths.makes hg B V.pupil.last V.pupil.P,
    limit, _root_.IssuedBridge.OriginalObservablePhases.original V.pupil.last V.pupil.P D rfl,
    fun lamp => SourceOnlyGraphSum.groupFiled hg V lamp⟩

def BeforeAll (hg : g.IsSimple) (H : g.core.Simple) (ε : ℝ) (a : YM.Axis)
    (O : YM.Integration.Election.OrderS g.core) (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core) : Prop :=
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
  ∃ E : Construction.{u} H ε a O, PhysicalMatching.H7OriginalWeakBookBudget.prediction c E.paths.kit ∧
    ∃ row : Row E, Fixed E row ∧ Clusters E row ∧
    ∀ (cohort : Ultrafilter (ℕ × ℕ) → Prop)
      (_issued : ∀ (ξ : YM.Extraction.Order) (l : Ultrafilter (ℕ × ℕ)),
        (l : Filter (ℕ × ℕ)) ≤ ξ.fuse → cohort l),
    ∃ pick : (ξ : YM.Extraction.Order) → Vision E ξ,
      (∀ ξ, Retained E cohort ξ (pick ξ)) ∧ (∀ ξ, Reads E row (pick ξ)) ∧
      (∀ (ξ : YM.Extraction.Order) (lamp : Bool), ∃ Q : Perspective H Z lamp, Q.MS = A ∧
        Vision.StandaloneCorrelation (pick ξ) Z A ∧ SourceOnlyGraphSum.EveryCoefficient Z A
          (YM.FVA2.Teller.logNu 1)) ∧ Receipts hg E pick

theorem original (hg : g.IsSimple) (a : YM.Axis) (H : g.core.Simple) {ε : ℝ} (positive : 0 < ε)
    (O : YM.Integration.Election.OrderS g.core) (c : PhysicalMatching.H7JointWeakBookPrices.Costs g.core) :
    BeforeAll.{u} hg H ε a O c := by
  obtain ⟨R,T,W,paid,budget⟩ := PhysicalMatching.H7JointVisionWeakBookElection.atCosts.{u} a H positive O c
  let E : Construction.{u} H ε a O := ⟨R,T,W,paid⟩
  obtain ⟨row,fixed,cluster⟩ := _root_.IssuedBridge.OriginalPointReturns.rows (g := g) E.receipts.paid
  refine ⟨E,budget,row,fixed,cluster,?_⟩
  intro cohort issued
  let chosen (ξ : YM.Extraction.Order) :=
    _root_.IssuedBridge.PostedElectedMatrixRetainedContinuumLimitVision.original E cohort issued ξ
  let pick (ξ : YM.Extraction.Order) : Vision E ξ := (chosen ξ).choose
  exact ⟨pick, fun ξ => (chosen ξ).choose_spec, fun ξ => reads E row cluster (pick ξ),
    fun ξ lamp => SourceOnlyGraphSum.groupFiled hg (pick ξ) lamp,
    onConstruction hg E row fixed cluster pick⟩

end YM.Answer.ContinuumLimit.PreElectedPublication

