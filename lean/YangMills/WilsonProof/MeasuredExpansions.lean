import YangMills.LatticeSections
import YangMills.PerturbativeMatching
import YangMills.WilsonProof.MeasuredFrames
import YangMills.WilsonProof.HierarchyChannels
import YangMills.WilsonProof.NativeGraph
import YangMills.WilsonProof.ReferenceOperands
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Estimates
import YangMills.WilsonProof.NativeSupport.OPEMatching.Estimates

noncomputable section
namespace YangMills.WilsonProof
open PerturbativeMatching Matching

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}
variable (reference : PerturbativeMatching.Reference g)
variable (H : CorrelationMatching.Measurement (maxwellReference g) T)

theorem channelsInFrame (physical : OPEMatching.PhysicalCoefficients H) :
    HasChannelBasis (measuredFrame H) := physical.channelBasis

theorem correlationInFrame
    (estimates : CorrelationMatching.Estimates g reference.scheme.conversion H) :
    CorrelationExpansion reference (measuredFrame H) := by
  refine ⟨estimates.tested, estimates.compact, estimates.derivatives, estimates.phaseAgreement, ?_⟩
  intro P ward
  exact estimates.stressExpansion P
    (wardOnSameCorrelations (M := reference.coefficients)
      (N := CorrelationMatching.coefficientTable g) (sameGraphArray g) _ _ ward)

theorem ordinaryInFrame (M : MSbar.Coefficients (maxwellReference g))
    (same : M.ope = reference.coefficients.ope)
    (estimates : OPEMatching.Estimates M reference.scheme.conversion H) :
    OPEExpansion reference (measuredFrame H) := by
  have converted {n : ℕ} (h k : ℕ) (a : Fin n → Label (maxwellReference g)) (x : Points n) :
      reference.scheme.conversion.ope M h k a x = reference.scheme.conversion.ope reference.coefficients h k a x :=
    convertedOPEOnSameArray same _ h k a x
  have transferred : OPEMatching.Estimates reference.coefficients reference.scheme.conversion H := by
    constructor
    · intro n h d
      simpa only [converted] using estimates.tested n h d
    · intro n h p d center K
      simpa only [OPEMatching.prediction, converted] using estimates.compact n h p d center K
    · intro n h p j d K
      simpa only [OPEMatching.prediction, converted] using estimates.derivatives n h p j d K
  exact ⟨transferred.tested, transferred.compact, transferred.derivatives⟩

end YangMills.WilsonProof
