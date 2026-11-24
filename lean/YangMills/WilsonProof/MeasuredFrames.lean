import YM.Euclid.Differential
import YangMills.PerturbativeMatching.Measurement
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Measurements

noncomputable section
namespace YangMills.WilsonProof
open PerturbativeMatching

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}
variable {B : Maxwell.Reference g}

def measuredFrame (H : CorrelationMatching.Measurement B T) : Measurement B T :=
  ⟨H.coupling, H.positive, H.oneLoop, H.frame, H.nested, H.frameAxes, H.unit,
    H.includeField, H.includeLabel, H.includeInsertion, H.multilinear⟩

theorem calibratedFrame (scheme : PositionScheme g)
    (H : CorrelationMatching.Measurement (maxwellReference g) T)
    (paid : CorrelationMatching.MeasuredNormalization scheme.prescription scheme.adjustment H) :
    ∃ J, FrameCalibration scheme (measuredFrame H) J := by
  obtain ⟨J, normalized, unique, unit, nested, real, integrable, coupling, fields⟩ := paid
  exact ⟨J, normalized, unique, unit, nested, real, integrable, coupling, fields⟩

end YangMills.WilsonProof
