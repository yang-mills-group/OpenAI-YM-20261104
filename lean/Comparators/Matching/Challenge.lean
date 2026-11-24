import YangMills.PerturbativeMatching

namespace YangMills

open PerturbativeMatching

/-- Every compact matrix gauge group with simple Lie algebra admits a Wilson
construction matching the MS-bar correlation functions and ordinary OPE. -/
theorem perturbativeMatching (g : GaugeGroup) (simple : g.IsSimple) :
    ∃ run : Wilson.Construction g, Nonempty (MatchedRun run) := by
  sorry

end YangMills
