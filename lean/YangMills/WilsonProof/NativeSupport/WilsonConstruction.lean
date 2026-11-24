import YangMills.WilsonProof.NativeSupport.ChallengeSpec

import YangMills.VolumeLimit
import YangMills.StressTensor
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! Families of Wilson limits and the distinguished volume refinement. -/

set_option autoImplicit false

noncomputable section

namespace YangMills.Wilson

def Construction.distinguished {g : GaugeGroup} (run : Construction g) :
    Hierarchy run.family :=
  (run.refine id (strictMono_id : StrictMono (id : ℕ → ℕ))).hierarchy

abbrev CoordinateFamily := (g : GaugeGroup) → g.IsSimple → Maxwell.Reference g

abbrev RunFamily := (g : GaugeGroup) → g.IsSimple → Construction g

structure Publication where
  coordinates : CoordinateFamily
  runs : RunFamily

end YangMills.Wilson
