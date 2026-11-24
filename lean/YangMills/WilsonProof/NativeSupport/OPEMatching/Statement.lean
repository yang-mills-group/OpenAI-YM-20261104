import YangMills.WilsonProof.NativeSupport.MatchingNesting
import YangMills.WilsonProof.NativeSupport.OPEMatching.Estimates
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Estimates
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Volume
import YangMills.WilsonProof.NativeSupport.FrameNormalization
import YangMills.WilsonProof.NativeSupport.YangMills.Existence

/-! Joint correlation and ordinary operator-product matching on Wilson volume
limits. The continuum reference is fixed before any lattice family is chosen.
Each refinement uses one measurement for both comparisons. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.OPEMatching

open Matching

variable {g : GaugeGroup}

/-- All short-distance assertions on a given hierarchy use these measured fields
and coupling, including the identification of the stress and its descendants. -/
structure MeasuredLimit (M : MSbar.Coefficients (maxwellReference g))
    (N : CorrelationMatching.Normalization g) {C : WilsonFamily g} {T : Hierarchy C}
    (H : CorrelationMatching.Measurement (maxwellReference g) T)
    (scaling : T.MaxwellScaling (maxwellReference g)) : Prop where
  normalization : CorrelationMatching.MeasuredNormalization N.prescription N.adjustment H
  sampling : ∀ k, scaling.frame k = H.frame (scaling.r k)
  fixedFields : FixedFields.Laws (maxwellReference g) T scaling
  maxwell : AllRadii.Laws (maxwellReference g) T scaling H.frame
  frameBounds : AllRadii.FrameBounds (maxwellReference g) T scaling H.frame
  correlations : CorrelationMatching.Estimates g N.conversion.conversion H
  coefficients : PhysicalCoefficients H
  operatorProducts : Estimates M N.conversion.conversion H

/-- On the selected volume limit, the physical coefficients control both a single
shrinking cluster and finite trees of independently shrinking clusters against separated exteriors. -/
structure OnRefinement (M : MSbar.Coefficients (maxwellReference g))
    (N : CorrelationMatching.Normalization g) {C : WilsonFamily g}
    (data : Wilson.WilsonData (maxwellReference g) C) (kernels : Wilson.PeriodPointTable C)
    (periods : ℕ → ℕ) (limit : Wilson.VolumeChoice C) : Prop where
  continuum : Wilson.ContinuumLimit data kernels (periods ∘ limit.indices) limit.hierarchy
  testLimits : CorrelationMatching.RepresentsTestLimits limit.hierarchy periods
  fusion : Hierarchy.SeparatedPowerLog limit.hierarchy
  nestedFusion : Hierarchy.SeparatedNestedPowerLog limit.hierarchy
  measurements : ∃ (H : CorrelationMatching.Measurement (maxwellReference g) limit.hierarchy)
      (scaling : limit.hierarchy.MaxwellScaling (maxwellReference g)), MeasuredLimit M N H scaling

/-- One regular Wilson family and one table of fixed-period limits serve every
strictly increasing request for periods. -/
structure OnConstruction (M : MSbar.Coefficients (maxwellReference g))
    (N : CorrelationMatching.Normalization g) (run : Wilson.Construction g) : Prop where
  regular : WilsonRegularity run.family
  trajectory : Wilson.WilsonTrajectory (maxwellReference g) run.family
  periods : ∃ (kernels : Wilson.PeriodPointTable run.family)
      (data : Wilson.WilsonData (maxwellReference g) run.family),
    CorrelationMatching.SmoothMeshLimit data ∧ Wilson.FixedPointReturns run.family kernels ∧ ∀ (p : ℕ → ℕ) (hp : StrictMono p),
      OnRefinement M N data kernels p (run.refine p hp)

/-- Existence and uniqueness of the ordinary MS-bar OPE are part of the goal.
The position calibration and stress Ward equations use the same graph
correlations that determine that OPE by exterior insertions. -/
def Matches (g : GaugeGroup) : Prop :=
  ∃ (existsReference : HasReference g) (N : CorrelationMatching.Normalization g),
    CorrelationMatching.GroupCalibration g N ∧
    (∃! P : WardStress.Series (maxwellReference g),
      CorrelationMatching.WardIdentities g N.conversion.conversion P) ∧
    ∃ run : Wilson.Construction g, OnConstruction (reference g existsReference) N run

/-- Read the correlation and single-cluster OPE estimates on the measurement
selected for this volume refinement. Both estimates use its calibrated coupling and fields. -/
theorem OnConstruction.estimatesOn {g : GaugeGroup} {M : MSbar.Coefficients (maxwellReference g)}
    {N : CorrelationMatching.Normalization g} {run : Wilson.Construction g}
    (matched : OPEMatching.OnConstruction M N run) (periods : ℕ → ℕ) (strict : StrictMono periods) :
    let T := (run.refine periods strict).hierarchy
    ∃ H : CorrelationMatching.Measurement (maxwellReference g) T,
      CorrelationMatching.MeasuredNormalization N.prescription N.adjustment H ∧
      CorrelationMatching.Estimates g N.conversion.conversion H ∧
      OPEMatching.Estimates M N.conversion.conversion H := by
  obtain ⟨_, _, _, _, refinements⟩ := matched.periods
  obtain ⟨H, _, laws⟩ := (refinements periods strict).measurements
  exact ⟨H, laws.normalization, laws.correlations, laws.operatorProducts⟩

/-- The OPE witness realizes the existence score with the identical lattice
family, raw tokens, period kernels and refinements. -/
theorem OnConstruction.realizes {M : MSbar.Coefficients (maxwellReference g)}
    {N : CorrelationMatching.Normalization g} {run : Wilson.Construction g}
    (h : OnConstruction M N run) : run.Realizes (maxwellReference g) := by
  obtain ⟨kernels, data, _, fixed, refinements⟩ := h.periods
  exact ⟨h.trajectory, data, kernels, fixed, fun p hp => (refinements p hp).continuum⟩


end YangMills.OPEMatching
