import YangMills.StressTensor

/-! One strictly increasing refinement and its continuum hierarchy for each requested sequence of physical volumes. -/
set_option autoImplicit false
noncomputable section

namespace YangMills.Wilson

structure VolumeChoice {g : GaugeGroup} (family : WilsonFamily g) where
  indices : ℕ → ℕ
  increasing : StrictMono indices
  hierarchy : Hierarchy family

structure Construction (g : GaugeGroup) where
  family : WilsonFamily g
  refine : (p : ℕ → ℕ) → StrictMono p → VolumeChoice family


end YangMills.Wilson
