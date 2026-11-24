import YM.Integration.WilsonGraphPaperPublication
import YM.Integration.WilsonGraphAppointedPosition
import YM.Integration.WilsonQ198PublicPhaseProximity
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.RestaffedMaxwellPublication

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonGraphPublishedReturnLaws
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


open YM.Integration.WilsonGraphPaperPublishedCorrelation (Paper OnRun)

open YM.Integration.WilsonGraphPaperPublication

abbrev measurementOnPick (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (p : ℕ → ℕ) (hp : StrictMono p) :=
  ElectedMeasurement.publicMeasurement hg (publicPick.{u} g hg (ElectedPublication.order p hp))
    (prescription g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)

theorem groupReadBack (g : YangMills.GaugeGroup)
    (M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g))
    (same : M.correlation = WilsonGraphStandaloneCorrelation.bare g) :
    WilsonGraphWardExtensional.SeparatedRead M (_root_.IssuedMaxwell.GraphCoefficients.issued g) := by
  intro n k v x hx
  rw [same]
  exact (WilsonGraphGroupPositionReference.agreement g n k v x hx).symm

theorem positionOnPick (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (p : ℕ → ℕ) (hp : StrictMono p) :
    let I := WilsonGraphGroupPositionReference.external g hg
    let run := (issued.{u}).runs g hg
    let choice := run.refine p hp
    YangMills.MSbar.CorrelationOnly.appointed I.menu I.realization run.family choice.hierarchy
      (measurementOnPick.{u} g hg p hp) :=
  ElectedMeasurement.appointed hg (publicPick.{u} g hg (ElectedPublication.order p hp))
    (WilsonGraphPaperPublication.perspective.{u} g hg)

theorem phaseOnPick (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (p : ℕ → ℕ) (hp : StrictMono p) :
    PhaseProximity (measurementOnPick.{u} g hg p hp) :=
  WilsonQ198PublicPhaseProximity.published hg (publicPick.{u} g hg (ElectedPublication.order p hp))
    (prescription g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)

theorem scalingOnPick (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (p : ℕ → ℕ) (hp : StrictMono p) :
    let B := YangMills.maxwellReference g
    let V := publicPick.{u} g hg (ElectedPublication.order p hp)
    let T := YangMills.hierarchy V.pupil.last V.pupil.P
    let Hₘ := measurementOnPick.{u} g hg p hp
    ∃ X : T.MaxwellScaling B, X.r = V.sc.r ∧
      (∀ k, X.frame k = Hₘ.frame (V.sc.r k)) ∧
      YangMills.FixedFields.Laws B T X ∧ YangMills.AllRadii.Laws B T X Hₘ.frame ∧
        YangMills.AllRadii.FrameBounds B T X Hₘ.frame :=
  RestaffedMaxwellPublication.original (publicPick.{u} g hg (ElectedPublication.order p hp))
    (prescription g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)

theorem returnedOnSeries (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (P₀ : YangMills.Matching.WardStress.Series (YangMills.maxwellReference g))
    (p : ℕ → ℕ) (hp : StrictMono p)
    (measured : namedStress (measurementOnPick.{u} g hg p hp) P₀) :
    Returned.{u} g hg P₀ p hp := by
  obtain ⟨X, _, _, fixed, radii, bounds⟩ := scalingOnPick.{u} g hg p hp
  exact ⟨positionOnPick.{u} g hg p hp, phaseOnPick.{u} g hg p hp,
    measured, X, fixed, radii, bounds⟩

theorem publicationOnSeries
    (P : (g : YangMills.GaugeGroup) → g.IsSimple →
      YangMills.Matching.WardStress.Series (YangMills.maxwellReference g))
    (paid : ∀ (g : YangMills.GaugeGroup) (hg : g.IsSimple),
      YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion (P g hg))
    (unique : ∀ (g : YangMills.GaugeGroup) (hg : g.IsSimple)
      (Q : YangMills.Matching.WardStress.Series (YangMills.maxwellReference g)),
      YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion Q → Q = P g hg)
    (measured : ∀ (g : YangMills.GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p),
      namedStress (measurementOnPick.{u} g hg p hp) (P g hg)) :
    WilsonGraphStandaloneCorrelation.OnPublication WilsonGraphGroupPositionReference.external
      (issued.{u}) := by
  apply WilsonGraphPaperPublication.assemble
  · intro g hg
    exact WilsonGraphPaperPublication.independentOnGroup g hg
      ⟨P g hg, paid g hg, fun Q accepted => unique g hg Q accepted⟩
  · intro g hg P₀ accepted p hp
    rw [unique g hg P₀ accepted]
    exact returnedOnSeries.{u} g hg (P g hg) p hp (measured g hg p hp)

end YM.Integration.WilsonGraphPublishedReturnLaws
end

