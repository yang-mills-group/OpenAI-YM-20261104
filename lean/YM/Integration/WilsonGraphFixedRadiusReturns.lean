import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PreElectedPublication
import YM.Integration.WilsonGraphAppointedPublicMeasurement
import YangMills.WilsonProof.NativeSupport.WilsonTestLimits

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonGraphFixedRadiusReturns

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open _root_.IssuedBridge
open scoped Topology BigOperators Classical ContDiff

open FVA2.GradedFar FVA2.Dframe
universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ}
variable {e : Axis} {O : OrderS g.core} {E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O}
variable {ξ : Extraction.Order}


open YangMills YangMills.Wilson YangMills.Matching

def tokens (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) {n : ℕ}
    (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i)) :
    Fin n → E.paths.family.book.Token :=
  by
    intro i
    let a : V.pupil.S.Tag := ElectedMeasurement.inputs V Z r d v i
    exact ⟨a.1, V.pupil.S.representative _ a.2⟩

theorem projected (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) {n : ℕ}
    (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i)) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).project ∘ tokens V Z r d v =
      ElectedMeasurement.inputs V Z r d v := by
  funext i
  change Sigma.mk (d i) (V.pupil.S.project (d i)
    (V.pupil.S.representative (d i) (ElectedMeasurement.frame V Z r (d i) (v i)))) =
    Sigma.mk (d i) (ElectedMeasurement.frame V Z r (d i) (v i))
  rw [V.pupil.S.rep]

def Observed {C : YangMills.WilsonFamily g} (F : PeriodPointTable C)
    (T : YangMills.Hierarchy C) (q : ℕ → ℕ) {n : ℕ}
    (w : Fin n → C.Token) (a : Fin n → T.Tag) : Prop :=
  T.project ∘ w = a ∧ (∀ m, Continuous (F m w)) ∧
  (∀ (m : ℕ) (t : YangMills.SeparatedTest n), C.suitable m t →
    Tendsto (fun N => C.smear N m w t) atTop (𝓝 (∫ z, t z * periodValue F m w z))) ∧
  (∀ (m : ℕ) (K : Set (YangMills.Points n)), IsCompact K → K ⊆ periodPatch C m n →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ z ∈ K, ∀ x,
      dist (nodePosition C N m x) z < δ →
      dist (C.finiteMoment N m w x) (periodValue F m w z) < ε) ∧
  (∀ K : Set (YangMills.Points n), IsCompact K → K ⊆ WilsonFamily.separated n →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
      dist (periodValue F (q k) w z) (T.correlation none a z) < ε) ∧
  (∀ t : YangMills.SeparatedTest n, (∀ᶠ k : ℕ in atTop, C.suitable (q k) t) ∧
    ∃ row : ℕ → ℂ,
      (∀ m, C.suitable m t → Tendsto (fun N => C.smear N m w t) atTop (𝓝 (row m))) ∧
      Tendsto (fun k => row (q k)) atTop (𝓝 (∫ x, t x * T.correlation none a x)))

theorem observed {C : YangMills.WilsonFamily g} (F : PeriodPointTable C)
    (fixed : FixedPointReturns C F) (T : YangMills.Hierarchy C) (q : ℕ → ℕ) {n : ℕ}
    (w : Fin n → C.Token) (a : Fin n → T.Tag) (sectionEq : T.project ∘ w = a)
    (volume : ∀ K : Set (YangMills.Points n), IsCompact K → K ⊆ WilsonFamily.separated n →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
        dist (periodValue F (q k) w z) (T.correlation none (T.project ∘ w) z) < ε)
    (tested : C.Converges q (fun v => T.correlation none (T.project ∘ v))) :
    Observed F T q w a := by
  refine ⟨sectionEq, fun m => fixed.regular m n w, fun m t ht => fixed.tested m n w t ht,
    fun m K hc hi ε he => fixed.fixedPeriod m n w K hc hi ε he, ?_, ?_⟩
  · simpa only [sectionEq] using volume
  · intro t
    simpa only [sectionEq] using tested n w t

theorem represented {C : YangMills.WilsonFamily g} (T : YangMills.Hierarchy C)
    {p q : ℕ → ℕ} (hq : StrictMono q) {n : ℕ} (w : Fin n → C.Token) (a : Fin n → T.Tag)
    (sectionEq : T.project ∘ w = a) (L : TestTable C) (pre : HasTestLimits C p L)
    (tested : C.Converges (p ∘ q) (fun v => T.correlation none (T.project ∘ v)))
    (t : YangMills.SeparatedTest n) : L n w t = ∫ x, t x * T.correlation none a x := by
  simpa only [sectionEq] using (representsTests_of_converging_refinement hq pre tested n w t)

theorem onRun (hg : g.IsSimple) (E : YM.Answer.ContinuumLimit.Construction.{u} H ε e O)
    (pick : (ξ : YM.Extraction.Order) → Vision E ξ)
    (receipts : YM.Answer.ContinuumLimit.PreElectedPublication.Receipts hg E pick) :
    let run := YM.Answer.ContinuumLimit.PreElectedPublication.publication E pick
    ∃ F : PeriodPointTable run.family, FixedPointReturns run.family F ∧
      ∀ (p : ℕ → ℕ) (hp : StrictMono p),
        let V := pick (ElectedPublication.order p hp)
        let chosen := run.refine p hp
        V.pupil.f.per.choose = p ∘ chosen.indices ∧ StrictMono chosen.indices ∧
        ∀ (Z : WilsonPrescription g.core) (r : ℝ) (n : ℕ) (d : Fin n → ℕ)
            (v : (i : Fin n) → (maxwellReference g).sector (d i)),
          let w := tokens V Z r d v
          let a := ElectedMeasurement.inputs V Z r d v
          Observed F chosen.hierarchy (p ∘ chosen.indices) w a ∧
          ∀ L : TestTable run.family, HasTestLimits run.family p L →
            ∀ t : YangMills.SeparatedTest n, L n w t = ∫ x, t x * chosen.hierarchy.correlation none a x := by
  let run := YM.Answer.ContinuumLimit.PreElectedPublication.publication E pick
  obtain ⟨_, _, ⟨F, fixed, outer⟩, returns⟩ := receipts
  refine ⟨F, fixed, ?_⟩
  intro p hp
  let V := pick (ElectedPublication.order p hp)
  let chosen := run.refine p hp
  obtain ⟨period, strict, _, _, _, tested, _, _⟩ := returns p hp
  refine ⟨period, strict, ?_⟩
  intro Z r n d v
  let w := tokens V Z r d v
  let a := ElectedMeasurement.inputs V Z r d v
  have sectionEq : chosen.hierarchy.project ∘ w = a := projected V Z r d v
  exact ⟨observed F fixed chosen.hierarchy (p ∘ chosen.indices) w a sectionEq
    (outer p hp n w) tested,
    fun L pre t => represented chosen.hierarchy strict w a sectionEq L pre tested t⟩

end YM.Integration.WilsonGraphFixedRadiusReturns

