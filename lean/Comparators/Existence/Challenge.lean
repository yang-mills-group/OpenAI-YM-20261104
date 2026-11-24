import YangMills.Existence

/-- Every compact matrix gauge group with simple Lie algebra admits a Wilson continuum
theory with a Maxwell ultraviolet limit and power-law fusion on every finite tree. -/
theorem YangMills.jointExistence (g : YangMills.GaugeGroup) (simple : g.IsSimple) :
    ∃ (free : YangMills.Maxwell.Reference g) (run : YangMills.Wilson.Construction g),
      run.Realizes free := by
  sorry
