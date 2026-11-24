import YM.MS.Shine.Ash
import YM.MS.Shine.Led
import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.House
import Mathlib.Analysis.Complex.RemovableSingularity
/-!
# Hards jet propagation from one contour at positive radius

Quantifies after weight/powers, no swapping Laurent and unregularized diagrams. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc Real Complex
open scoped Topology ContDiff
variable {A I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F]
variable {c:ℂ}{R T:ℝ} {u: I → ℂ} {f:ℂ→ E→F} {x:I→ℂ}
-- to Rise
end YM.MS.Shine
