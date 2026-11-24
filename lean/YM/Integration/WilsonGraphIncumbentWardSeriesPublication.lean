import YM.Integration.WilsonGraphPublishedReturnLaws
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandalonePublishedWardGroupSeries
import YM.Integration.WilsonGraphWardGroundPupils
import YM.Integration.WilsonGraphAppointedWardGroundMatrix
import YM.Integration.WilsonGraphWardGroundMatrix
import YM.Integration.WilsonGraphWardFourGroundTests
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellWardAction

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonGraphIncumbentWardSeriesPublication
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


open WilsonGraphPaperPublication WilsonGraphPublishedReturnLaws

def groupPupils (g : YangMills.GaugeGroup) (hg : g.IsSimple) :
    PhysicalMatching.H7StandaloneFourSmearedWardReadings.Pupils :=
  WilsonGraphWardGroundPupils.pupils (g := g) (_root_.IssuedMaxwell.ElectedPrescription.simple g hg)

def groundMatrix (g : YangMills.GaugeGroup) (hg : g.IsSimple) : Matrix (Fin 4) (Fin 4) ℂ :=
  PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients.matrixCoefficients
    (prescription g hg) (WilsonGraphPaperPublication.perspective.{u} g hg) (groupPupils g hg) 0

def series (g : YangMills.GaugeGroup) (hg : g.IsSimple) :
    YangMills.Matching.WardStress.Series (YangMills.maxwellReference g) :=
  PhysicalMatching.H7StandaloneAppointedWardStressSeries.selected
    (prescription g hg) (WilsonGraphPaperPublication.perspective.{u} g hg) (groupPupils g hg) (groundMatrix.{u} g hg)

def leadingRows (g : YangMills.GaugeGroup) (hg : g.IsSimple) : Prop :=
  let L := groundMatrix.{u} g hg
  ∀ i j, L i j = PhysicalMatching.H7IndependentFourMaxwellWardReadings.leading (L 3 1) (L 3 2) i j

def groundTests (g : YangMills.GaugeGroup) (hg : g.IsSimple) : Prop :=
  let H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  let S := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion
  let P := groupPupils g hg
  WilsonGraphWardGroundMatrix.Tested S H 0 (fun i : Fin 0 => Fin.elim0 i)
      id (fun x => P.vacuum x) ∧
    (∀ row j : Fin 2, ∀ a : YM.Axis, WilsonGraphWardGroundMatrix.Tested S H a
      (fun _ : Fin 1 => j) id
      (fun x => YangMills.Ward.firstDerivative a (fun y => P.conservation row j y) x)) ∧
    ∀ a : YM.Axis, WilsonGraphWardGroundMatrix.Tested S H a (fun _ : Fin 2 => 0)
      (fun z : YangMills.Spacetime × YangMills.Points 2 => YangMills.Ward.prepend z.1 z.2)
      (fun z => P.translation z.2 * ((YangMills.Maxwell.partialD a P.cutoff z.1 : ℝ) : ℂ))

theorem filedOnGroup (g : YangMills.GaugeGroup) (hg : g.IsSimple) :
    (WilsonGraphGroupPositionReference.external g hg).conversion.conversion =
      _root_.IssuedBridge.PostedAppointedConversion.filed (prescription g hg)
        (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.perspective.{u} g hg).matching (YM.FVA2.Teller.logNu 1) := by
  exact congrArg
    (fun F : YangMills.MSbar.PositionConversion (YangMills.maxwellReference g) => F.conversion)
    (WilsonGraphGroupPositionReference.atPerspective hg
      (WilsonGraphPaperPublication.perspective.{u} g hg)
      (WilsonGraphPaperPublication.nominated.{u} g hg))

theorem wardOnPick (g : YangMills.GaugeGroup) (hg : g.IsSimple) (leading : leadingRows.{u} g hg)
    (p : ℕ → ℕ) (hp : StrictMono p) :
    YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion (series.{u} g hg) ∧
      namedStress (measurementOnPick.{u} g hg p hp) (series.{u} g hg) := by
  rw [filedOnGroup.{u} g hg]
  exact PhysicalMatching.H7StandaloneAppointedWardGroupSeries.onPublishedVolume
    (publicPick.{u} g hg (ElectedPublication.order p hp)) (prescription g hg)
    (WilsonGraphPaperPublication.perspective.{u} g hg) none 0 (groupPupils g hg) leading

theorem groupUnique (g : YangMills.GaugeGroup) (hg : g.IsSimple) (leading : leadingRows.{u} g hg)
    (tests : groundTests g hg)
    {P Q : YangMills.Matching.WardStress.Series (YangMills.maxwellReference g)}
    (first : YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
      (WilsonGraphGroupPositionReference.external g hg).conversion.conversion P)
    (second : YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
      (WilsonGraphGroupPositionReference.external g hg).conversion.conversion Q) : P = Q := by
  let H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  let S := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion
  let T := groupPupils g hg
  let L := groundMatrix.{u} g hg
  have matrixRead : WilsonGraphWardGroundMatrix.matrix S H T = L := by
    have same := congrArg
      (fun K : YangMills.Matching.Conversion (_root_.IssuedMaxwell.Reports.B g) =>
        WilsonGraphWardGroundMatrix.matrix K H T) (filedOnGroup.{u} g hg)
    exact same.trans (WilsonGraphAppointedWardGroundMatrix.atPupils
      (Z := prescription g hg) (Q := WilsonGraphPaperPublication.perspective.{u} g hg) T)
  have injective : Function.Injective (PhysicalMatching.H7StandaloneFiniteWardMatrix.act L) := by
    intro v w same
    calc
      v = PhysicalMatching.H7StandaloneFiniteWardMatrix.act L (PhysicalMatching.H7StandaloneFiniteWardMatrix.act L v) :=
        (PhysicalMatching.H7IndependentFiledMaxwellWardAction.actualTwice L leading v).symm
      _ = PhysicalMatching.H7StandaloneFiniteWardMatrix.act L (PhysicalMatching.H7StandaloneFiniteWardMatrix.act L w) :=
        congrArg (PhysicalMatching.H7StandaloneFiniteWardMatrix.act L) same
      _ = w := PhysicalMatching.H7IndependentFiledMaxwellWardAction.actualTwice L leading w
  obtain ⟨vacuum, conservation, translation⟩ := tests
  refine WilsonGraphWardFourGroundTests.unique H T L ?_ injective first second
  intro v w
  rw [← matrixRead]
  exact WilsonGraphWardGroundMatrix.groundRows S H T vacuum conservation translation v w

theorem publication
    (leading : ∀ (g : YangMills.GaugeGroup) (hg : g.IsSimple), leadingRows.{u} g hg)
    (tests : ∀ (g : YangMills.GaugeGroup) (hg : g.IsSimple), groundTests g hg) :
    WilsonGraphStandaloneCorrelation.OnPublication WilsonGraphGroupPositionReference.external
      (issued.{u}) := by
  have paid (g : YangMills.GaugeGroup) (hg : g.IsSimple) :
      YangMills.Matching.WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion (series.{u} g hg) :=
    (wardOnPick.{u} g hg (leading g hg) (fun i : ℕ => i) (fun _ _ h => h)).1
  refine WilsonGraphPublishedReturnLaws.publicationOnSeries.{u} series.{u} paid ?_ ?_
  · intro g hg Q accepted
    exact groupUnique.{u} g hg (leading g hg) (tests g hg) accepted (paid g hg)
  · intro g hg p hp
    exact (wardOnPick.{u} g hg (leading g hg) p hp).2

end YM.Integration.WilsonGraphIncumbentWardSeriesPublication
end

