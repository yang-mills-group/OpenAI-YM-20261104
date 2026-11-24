import YangMills.WilsonProof.ReferenceOperands
import YangMills.WilsonProof.NativeSupport.WilsonFlashScoredGroupReference

set_option autoImplicit false
noncomputable section
namespace YangMills.WilsonProof
open PerturbativeMatching MSbar Matching
open YM.Integration

abbrev electedScheme (g : GaugeGroup) (hg : g.IsSimple) : PositionScheme g :=
  let N := WilsonFlashScoredGroupReference.normalization g hg
  ⟨N.prescription, N.conversion, N.adjustment⟩

def electedReference (g : GaugeGroup) (hg : g.IsSimple) : Reference g := by
  let determined := graphDetermined (WilsonFlashScoredGroupReference.determined g hg)
  let S := electedScheme g hg
  have same : (CorrelationMatching.coefficientTable g).correlation =
      (msbarCoefficients g determined).correlation := (sameGraphArray g).symm
  have old := WilsonFlashScoredGroupReference.calibrated g hg
  refine ⟨determined, S, old.nominated, ?_, ?_⟩
  · apply calibrationOnSameCorrelations same S
    exact ⟨old.admissible, old.signedSlope, old.conversionValid, old.adjustmentValue⟩
  · obtain ⟨stress, identity, unique⟩ := WilsonFlashScoredGroupReference.stress g hg
    refine ⟨stress, wardOnSameCorrelations same S.conversion stress identity, ?_⟩
    exact fun candidate law => unique candidate (wardOnSameCorrelations same.symm S.conversion candidate law)

theorem issuedOPE (g : GaugeGroup) (hg : g.IsSimple) :
    (electedReference g hg).coefficients.ope = (_root_.IssuedMaxwell.GraphCoefficients.issued g).ope := by
  have old := WilsonFlashScoredGroupReference.determined g hg
  have valid := MSbar.Ordinary.read_valid (maxwellReference g) old
  exact (graphOPE (electedReference g hg).opeDetermined _ valid).symm.trans
    (WilsonFlashScoredGroupReference.issued g hg)

end YangMills.WilsonProof
