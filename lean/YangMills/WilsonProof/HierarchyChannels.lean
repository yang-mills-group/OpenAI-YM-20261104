import YangMills.CorrelationHierarchy

namespace YangMills.Hierarchy

/-- The field belonging to the channel in the original measured coefficient. -/
abbrev actor {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (d : ℕ) :
    T.Channel d → T.Field d := T.channelField d

end YangMills.Hierarchy
