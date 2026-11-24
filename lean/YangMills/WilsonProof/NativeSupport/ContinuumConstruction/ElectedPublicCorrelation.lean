import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicRunning
import YangMills.WilsonProof.NativeSupport.IssuedBridge.FullPhysicalProperties
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.ConstructedGroupGraphSum
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalPointReturns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalQuotient
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalObservablePhases
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedGroupCalendar
import YangMills.WilsonProof.NativeSupport.IssuedRuns.OriginalTrajectory
import YangMills.WilsonProof.NativeSupport.MaxwellBridge

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Answer.ContinuumLimit.ElectedPublication
open Filter Function Set
open YangMills YangMills.Wilson
open scoped Topology
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : YM.Axis}
  {O : YM.Integration.Election.OrderS g.core}

def order (p : ℕ → ℕ) (hp : StrictMono p) : YM.Extraction.Order := ⟨.full, ⟨p, hp⟩⟩

def appointed (E : Construction.{u} H ε e O) (p : ℕ → ℕ) (hp : StrictMono p) : Vision E (order p hp) :=
  Classical.choice (afterElection E (order p hp))

def publication (E : Construction.{u} H ε e O) : YangMills.Wilson.Construction g where
  family := YangMills.wilsonFamily E.paths.family
  refine p hp := let V := appointed E p hp
                 ⟨V.g.per.choose, V.g.per.monotone, YangMills.hierarchy V.pupil.last V.pupil.P⟩

theorem period {E : Construction.{u} H ε e O} {p : ℕ → ℕ} {hp : StrictMono p}
    (V : Vision E (order p hp)) : V.pupil.f.per.choose = p ∘ V.g.per.choose := by
  exact congrArg (fun ξ : YM.Extraction.Order => ξ.per.choose) V.usesP

theorem points (E : Construction.{u} H ε e O) : (publication E).originalPointReturns := by
  obtain ⟨row, fixed, cluster⟩ := _root_.IssuedBridge.OriginalPointReturns.rows (g := g) E.receipts.paid
  refine ⟨_root_.IssuedBridge.PhysicalPeriodNodes.appoint E.paths.family row, fixed, ?_⟩
  intro p hp n v K compact inside δ pos
  let V := appointed E p hp
  have measured := _root_.IssuedBridge.OriginalPointReturns.outer (g := g) H
    V.pupil.last V.pupil.P row cluster n v K compact inside δ pos
  rw [period V] at measured
  exact measured

def Receipts (hg : g.IsSimple) (E : Construction.{u} H ε e O) : Prop :=
  let B := YangMills.maxwellReference g
  let run := publication E
  let D := _root_.IssuedRuns.FinalWilsonData.original E.paths.family E.paths.makes hg B
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let A := YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core
  WilsonRegularity run.family ∧
  WilsonTrajectory B run.family ∧ run.originalPointReturns ∧
  ∀ (p : ℕ → ℕ) (hp : StrictMono p),
    let V := appointed E p hp
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

theorem onConstruction (hg : g.IsSimple) (E : Construction.{u} H ε e O) : Receipts hg E := by
  let B := YangMills.maxwellReference g
  let D := _root_.IssuedRuns.FinalWilsonData.original E.paths.family E.paths.makes hg B
  refine ⟨D.regular, _root_.IssuedRuns.OriginalTrajectory.original E.paths.family E.paths.makes hg B,
    points E, ?_⟩
  intro p hp
  let V := appointed E p hp
  let Y := YangMills.hierarchy V.pupil.last V.pupil.P
  have limit := YangMills.wilsonLimit V.pupil.last V.pupil.P V.pupil.trackP
  change (YangMills.wilsonFamily E.paths.family).Converges V.pupil.f.per.choose
    (fun v => Y.correlation none (Y.project ∘ v)) at limit
  rw [period V] at limit
  exact ⟨period V, V.g.per.monotone, V.pupil.TrackU, V.pupil.trackP,
    _root_.IssuedBridge.OriginalQuotient.original E.paths.makes hg B V.pupil.last V.pupil.P,
    limit, _root_.IssuedBridge.OriginalObservablePhases.original V.pupil.last V.pupil.P D rfl,
    fun lamp => SourceOnlyGraphSum.groupFiled hg V lamp⟩

theorem original (g : YangMills.GaugeGroup) (hg : g.IsSimple) :
    ∃ E : Construction.{u} (_root_.IssuedMaxwell.ElectedPrescription.simple g hg)
      1 YM.timeAxis (_root_.IssuedBridge.PostedGroupCalendar.schedule g), Receipts hg E := by
  obtain ⟨E⟩ := Construct.{u} (_root_.IssuedMaxwell.ElectedPrescription.simple g hg) 1
    YM.timeAxis (_root_.IssuedBridge.PostedGroupCalendar.schedule g) zero_lt_one
  exact ⟨E, onConstruction hg E⟩

end YM.Answer.ContinuumLimit.ElectedPublication
