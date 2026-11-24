import YM.Integration.WilsonGraphWardExtensional
import YM.Integration.WilsonGraphPaperCorrelations

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonGraphPaperPublication
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

def Independent (g : YangMills.GaugeGroup) (hg : g.IsSimple) : Prop :=
  let B := YangMills.maxwellReference g
  let I := WilsonGraphGroupPositionReference.external g hg
  ∃ P₀ : YangMills.Matching.WardStress.Series B,
    YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        I.conversion.conversion P₀ ∧
    ∀ M : YangMills.MSbar.Coefficients B, M.correlation = WilsonGraphStandaloneCorrelation.bare g →
      YangMills.Matching.WardStress.Determined M I.conversion.conversion P₀ ∧
        ∀ P : YangMills.Matching.WardStress.Series B,
          YangMills.Matching.WardStress.Determined M I.conversion.conversion P → P = P₀

theorem independentOnGroup (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (ground : ∃! P : YangMills.Matching.WardStress.Series (YangMills.maxwellReference g),
      YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion P) :
    Independent g hg :=
  WilsonGraphWardExtensional.oneSeries
    (WilsonGraphGroupPositionReference.external g hg).conversion.conversion
    (_root_.IssuedMaxwell.GraphCoefficients.issued g) (WilsonGraphStandaloneCorrelation.bare g)
    (fun k v x hx => WilsonGraphGroupPositionReference.agreement g _ k v x hx) ground

def Returned (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (P₀ : YangMills.Matching.WardStress.Series (YangMills.maxwellReference g))
    (p : ℕ → ℕ) (hp : StrictMono p) : Prop :=
  let B := YangMills.maxwellReference g
  let I := WilsonGraphGroupPositionReference.external g hg
  let Q := perspective.{u} g hg
  let Z := prescription g hg
  let run := (issued.{u}).runs g hg
  let choice := run.refine p hp
  let V := publicPick.{u} g hg (ElectedPublication.order p hp)
  let Hₘ := ElectedMeasurement.publicMeasurement hg V Z Q
  YangMills.MSbar.CorrelationOnly.appointed I.menu I.realization run.family choice.hierarchy Hₘ ∧
    PhaseProximity Hₘ ∧
    namedStress Hₘ P₀ ∧
    ∃ X : choice.hierarchy.MaxwellScaling B, YangMills.FixedFields.Laws B choice.hierarchy X ∧
      YangMills.AllRadii.Laws B choice.hierarchy X Hₘ.frame ∧
      YangMills.AllRadii.FrameBounds B choice.hierarchy X Hₘ.frame

theorem namedOnEveryVolume (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (independent : Independent g hg)
    (returned : ∀ P₀ : YangMills.Matching.WardStress.Series (YangMills.maxwellReference g),
      YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion P₀ →
      ∀ (p : ℕ → ℕ) (hp : StrictMono p), Returned.{u} g hg P₀ p hp) :
    let B := YangMills.maxwellReference g
    let I := WilsonGraphGroupPositionReference.external g hg
    ∃ P₀ : YangMills.Matching.WardStress.Series B,
      YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
          I.conversion.conversion P₀ ∧
      (∀ M : YangMills.MSbar.Coefficients B, M.correlation = WilsonGraphStandaloneCorrelation.bare g →
        YangMills.Matching.WardStress.Determined M I.conversion.conversion P₀ ∧
        ∀ P : YangMills.Matching.WardStress.Series B,
          YangMills.Matching.WardStress.Determined M I.conversion.conversion P → P = P₀) ∧
      ∀ (p : ℕ → ℕ) (hp : StrictMono p),
        let V := publicPick.{u} g hg (ElectedPublication.order p hp)
        namedStress (ElectedMeasurement.publicMeasurement hg V (prescription g hg) (perspective.{u} g hg)) P₀ := by
  obtain ⟨P₀, original, models⟩ := independent
  exact ⟨P₀, original, models, fun p hp => (returned P₀ original p hp).2.2.1⟩

theorem assemble (independent : ∀ (g : YangMills.GaugeGroup) (hg : g.IsSimple), Independent g hg)
    (returned : ∀ (g : YangMills.GaugeGroup) (hg : g.IsSimple)
      (P₀ : YangMills.Matching.WardStress.Series (YangMills.maxwellReference g)),
      YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion P₀ →
      ∀ (p : ℕ → ℕ) (hp : StrictMono p), Returned.{u} g hg P₀ p hp) :
    WilsonGraphStandaloneCorrelation.OnPublication WilsonGraphGroupPositionReference.external
      (issued.{u}) := by
  intro g hg
  let B := YangMills.maxwellReference g
  let I := WilsonGraphGroupPositionReference.external g hg
  let E := construction.{u} g hg
  let Z := prescription g hg
  let Q := perspective.{u} g hg
  let D := _root_.IssuedRuns.FinalWilsonData.original E.paths.family E.paths.makes hg B
  obtain ⟨P₀,ground,models⟩ := independent g hg
  obtain ⟨coordinates,regular,trajectory,points,priced⟩ := correlations.{u} g hg
  refine ⟨coordinates,regular,trajectory,points,D,?_⟩
  intro p hp
  let V := publicPick.{u} g hg (ElectedPublication.order p hp)
  let Hₘ := ElectedMeasurement.publicMeasurement hg V Z Q
  obtain ⟨converges,adjoint,phases,all⟩ := priced p hp
  obtain ⟨appointed,phasePrice,named,X,fixed,radii,bounds⟩ := returned g hg P₀ ground p hp
  exact ⟨converges,adjoint,phases,Hₘ,X,appointed,
    fun M read => correlationsWithWard M I.conversion.conversion Hₘ (all M read) phasePrice
      ⟨P₀, (models M read).1, (models M read).2⟩
      (fun P paid => by rw [(models M read).2 P paid]; exact named),fixed,radii,bounds⟩

end YM.Integration.WilsonGraphPaperPublication
end

