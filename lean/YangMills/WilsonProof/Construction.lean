import YangMills.WilsonProof.PublishedLattice
import YangMills.WilsonProof.ElectedTree
import YangMills.WilsonProof.ReferenceElection
import YangMills.WilsonProof.MeasuredExpansions
import YangMills.WilsonProof.SampledCoordinates
import YangMills.WilsonProof.TestLimits
import YangMills.WilsonProof.NativeSupport.WilsonFlashScoredOrdinaryEstimates
import YangMills.WilsonProof.NativeSupport.WilsonFlashScoredSingleFusion
import YangMills.WilsonProof.NativeSupport.WilsonFlashScoredChannels
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeOnThePublishedReader
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Construction.MeasuredNormalization
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Construction.PhysicalHierarchy
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Construction.LocalLaws
import YM.Integration.WilsonGraphFixedRadiusReturns
import YM.Integration.WilsonFlashOnBothPublishedRows

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace YangMills.WilsonProof
open PerturbativeMatching Filter
open YM.Integration YM.Integration.WilsonGraphPaperPublication
open YM.Integration.WilsonGraphPublishedReturnLaws
open scoped Topology Classical

private theorem refinementOnPublishedRun (g : GaugeGroup) (hg : g.IsSimple)
    (periods : ℕ → ℕ) (strict : StrictMono periods) :
    Nonempty (MatchedRefinement (electedReference g hg) (publishedLattice g hg)
      (publishedKernels g hg) periods ((publishedRun g hg).refine periods strict)) := by
  let V := publicPick.{0} g hg (YM.Answer.ContinuumLimit.ElectedPublication.order periods strict)
  let choice := (publishedRun g hg).refine periods strict
  let H := CorrelationMatching.Construction.measurement (measurementOnPick.{0} g hg periods strict)
  let reference := electedReference g hg
  let F := publishedKernels g hg
  let D := publishedLattice g hg
  obtain ⟨indices, increasing, _, _, adjoint, tested, phases, _⟩ :=
    (WilsonGraphIncumbentGraphPublication.atPeriods.{0} g hg).2.2.2.choose_spec.2 periods strict
  obtain ⟨reconstruction, tables, vacua⟩ :=
    CorrelationMatching.Construction.physicalHierarchy.{0} g hg periods strict
  obtain ⟨ope, ward, trace⟩ := CorrelationMatching.Construction.localLaws g hg periods strict
  obtain ⟨X, radii, frames, fixed, maxwell, bounds⟩ := scalingOnPick.{0} g hg periods strict
  obtain ⟨J, calibration⟩ := calibratedFrame reference.scheme H
    (CorrelationMatching.Construction.measuredNormalization.{0} g hg periods strict)
  have pointwise (n : ℕ) (labels : Fin n → (publishedRun g hg).family.Token) := by
    let order := YM.Answer.ContinuumLimit.ElectedPublication.order periods strict
    have selected := ((rowBefore.{0} g hg).choose_spec.2.2
      (fun _ => True) (fun _ _ _ => True.intro)).choose_spec
    have limit := selected.2.1 order n labels
    change ∀ K : Set (Points n), IsCompact K → K ⊆ WilsonFamily.separated n →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
        dist (Wilson.periodValue F (V.pupil.f.per.choose k) labels x)
          (choice.hierarchy.correlation none (choice.hierarchy.project ∘ labels) x) < ε at limit
    rw [show V.pupil.f.per.choose = periods ∘ choice.indices from indices] at limit
    exact limit
  let continuum : Wilson.ContinuumLimit D F (periods ∘ choice.indices) choice.hierarchy := {
    smeared := tested
    pointwise := pointwise
    reconstruction := reconstruction
    fieldSpace := tables
    vacuumSectors := vacua
    adjoints := adjoint
    phaseCorrelations := phases
    ope := ope
    coefficients := publicCoefficientLaws V.pupil.last V.pupil.P
    fusionTrees := powerTreesOnPublishedRefinement g hg periods strict
    ward := ward
    trace := trace
    ultraviolet := AllRadii.maxwellLimit (maxwellReference g) choice.hierarchy X H.frame fixed maxwell bounds }
  let M := OPEMatching.reference g (WilsonFlashScoredGroupReference.determined g hg)
  have same : M.ope = reference.coefficients.ope :=
    (WilsonFlashScoredGroupReference.issued g hg).trans (issuedOPE g hg).symm
  refine ⟨{
    continuum := continuum
    testLimits := testLimitsOnRefinement increasing tested
    singleCluster := WilsonFlashScoredSingleFusion.original.{0} g hg periods strict
    fusionTrees := WilsonSharpPhysicalTreeOnThePublishedReader.original.{0} g hg periods strict
    measurement := measuredFrame H
    positionFrame := J
    calibration := calibration
    channelBasis := channelsInFrame H (WilsonFlashScoredChannels.physical.{0} g hg periods strict)
    scaling := X
    sampledFrame := ?_
    fixedFields := fixed
    maxwellLimit := maxwell
    frameBounds := bounds
    correlations := correlationInFrame reference H
      (CorrelationMatching.Construction.graphEstimates.{0} g hg periods strict)
    operatorProducts := ordinaryInFrame reference H M same
      (WilsonFlashScoredOrdinaryEstimates.estimates.{0} g hg periods strict
        (YM.FVA2.GradedFar.AppointedFlashNumerator.allJets g hg periods strict)) }⟩
  intro k
  rw [radii]
  exact frames k

theorem matchedRun (g : GaugeGroup) (hg : g.IsSimple) : Nonempty (MatchedRun (publishedRun g hg)) :=
  ⟨{ reference := electedReference g hg
     lattice := publishedLattice g hg
     kernels := publishedKernels g hg
     trajectory := (WilsonGraphIncumbentGraphPublication.atPeriods.{0} g hg).2.1
     admissible := admissibleOnPublishedLattice g hg
     meshLimit := smoothOnPublishedLattice g hg
     fixedPeriodLimits := (rowBefore.{0} g hg).choose_spec.1
     refinement := fun p hp => Classical.choice (refinementOnPublishedRun g hg p hp) }⟩

end YangMills.WilsonProof
