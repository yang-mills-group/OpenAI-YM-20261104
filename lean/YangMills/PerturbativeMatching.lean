import YangMills.Existence
import YangMills.PhysicalOPE.FusionTree
import YangMills.PerturbativeMatching.Correlations
import YangMills.PerturbativeMatching.OperatorProducts
import YangMills.PerturbativeMatching.NativeLattice
import YangMills.PerturbativeMatching.VolumeLimits
import YangMills.ScalingLimits

/-! Wilson Yang–Mills matching on every selected continuum refinement. -/

set_option autoImplicit false

namespace YangMills.PerturbativeMatching

variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The physical hierarchy and the two short-distance expansions on one refinement.
The period limits use the selected subsequence. The test-table law also accounts
for every table that already converges on the requested sequence. -/
structure MatchedRefinement (reference : Reference g)
    (lattice : Wilson.WilsonData (maxwellReference g) C) (kernels : Wilson.PeriodPointTable C)
    (periods : ℕ → ℕ) (limit : Wilson.VolumeChoice C) where
  continuum : Wilson.ContinuumLimit lattice kernels (periods ∘ limit.indices) limit.hierarchy
  testLimits : RepresentsTestLimits limit.hierarchy periods
  singleCluster : Hierarchy.SeparatedPowerLog limit.hierarchy
  fusionTrees : Hierarchy.SeparatedNestedPowerLog limit.hierarchy

  measurement : Measurement (maxwellReference g) limit.hierarchy
  positionFrame : MSbar.PositionFrames limit.hierarchy (maxwellReference g)
  calibration : FrameCalibration reference.scheme measurement positionFrame
  channelBasis : HasChannelBasis measurement

  scaling : limit.hierarchy.MaxwellScaling (maxwellReference g)
  sampledFrame (k : ℕ) : scaling.frame k = measurement.frame (scaling.r k)
  fixedFields : FixedFields.Laws (maxwellReference g) limit.hierarchy scaling
  maxwellLimit : AllRadii.Laws (maxwellReference g) limit.hierarchy scaling measurement.frame
  frameBounds : AllRadii.FrameBounds (maxwellReference g) limit.hierarchy scaling measurement.frame

  correlations : CorrelationExpansion reference measurement
  operatorProducts : OPEExpansion reference measurement

/-- One perturbative reference and one set of microscopic Wilson data serve
every requested period sequence. The run selects the refinement. -/
structure MatchedRun (run : Wilson.Construction g) where
  reference : Reference g
  lattice : Wilson.WilsonData (maxwellReference g) run.family
  kernels : Wilson.PeriodPointTable run.family
  trajectory : Wilson.WilsonTrajectory (maxwellReference g) run.family
  admissible : AdmissibleLattice lattice
  meshLimit : SmoothMeshLimit run.family kernels
  fixedPeriodLimits : Wilson.FixedPointReturns run.family kernels
  refinement (periods : ℕ → ℕ) (increasing : StrictMono periods) :
    MatchedRefinement reference lattice kernels periods (run.refine periods increasing)

/-- The same run and volume choices realize continuum existence. -/
theorem MatchedRun.realizes {run : Wilson.Construction g} (matched : MatchedRun run) :
    run.Realizes (maxwellReference g) :=
  ⟨matched.trajectory, matched.lattice, matched.kernels, matched.fixedPeriodLimits,
    fun periods increasing => (matched.refinement periods increasing).continuum⟩

end YangMills.PerturbativeMatching
