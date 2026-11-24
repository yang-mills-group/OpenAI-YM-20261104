import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellProfiles
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentIntegratedMaxwellWardPupils
import YM.Gauge.Casimir

set_option autoImplicit false

noncomputable section

namespace YM.Integration.WilsonGraphWardGroundPupils

open _root_.YangMills
open _root_.PhysicalMatching.H7IndependentFiledMaxwellProfiles (price)
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils)

variable {g : GaugeGroup}

/-- The normalized magnetic two-point kernel has positive price for this group. -/
theorem pricePositive (H : g.core.Simple) : 0 < price g.core := by
  have hdim : g.core.lieDim ≠ 0 := by
    intro hzero
    have hcasimir := _root_.YM.Gauge.casimir_pos H
    simp [_root_.YM.Gauge.casimir, hzero] at hcasimir
  have hdimReal : 0 < (g.core.lieDim : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hdim
  exact mul_pos (mul_pos (by norm_num) hdimReal)
    (pow_pos _root_.YM.Maxwell.normal_pos 2)

/-- The four separated test functions selected before the physical run. -/
def pupils (H : g.core.Simple) : Pupils :=
  _root_.PhysicalMatching.H7IndependentIntegratedMaxwellWardPupils.pupils
    (price g.core) (pricePositive H)

end YM.Integration.WilsonGraphWardGroundPupils

end

