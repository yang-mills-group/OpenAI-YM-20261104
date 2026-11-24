import YangMills.ShortDistance
import YangMills.ScalingLimits

set_option autoImplicit false
noncomputable section
namespace YangMills.AllRadii
open Filter Set
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : WilsonFamily g} (B : Maxwell.Reference g) (T : Hierarchy C)

/-- Express the sampled bounds and their continuous-radius extension in the same coordinates. -/
theorem maxwellLimit (X : T.MaxwellScaling B) (J : ℝ → Frame B T)
    (fixed : FixedFields.Laws B T X) (all : Laws B T X J) (bounds : FrameBounds B T X J) :
    ∃ S : ShortDistance.Coordinates B T, ShortDistance.MaxwellLimit B T S := by
  let S : ShortDistance.Coordinates B T := ⟨X.r, X.positive, X.later, X.drips, J⟩
  have samples : S.sample = X.frame := funext all.restricts
  refine ⟨S, ?_, ?_, ?_, all.mixed⟩
  · change ShortDistance.FixedFieldLaws B T X.r S.sample
    rw [samples]
    exact ⟨fixed.phaseBound, fixed.phaseDerivatives, fixed.unit, fixed.stress, fixed.derivatives,
      fixed.finiteReadings, fixed.limit⟩
  · change ShortDistance.FrameBounds B T (J (X.r 0)) J
    rw [all.restricts 0]
    exact ⟨bounds.forward, bounds.inverse⟩
  · intro a b
    simpa only [S, all.restricts 0] using all.stress a b
end YangMills.AllRadii
