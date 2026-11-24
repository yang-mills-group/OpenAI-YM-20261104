import YM.MS.Arc.Leaves

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology Interval
variable {E F: Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
def pruning (b:ℕ) (f:Tree E F): Tree E F:= chop^[b] f
end YM.MS.Arc
