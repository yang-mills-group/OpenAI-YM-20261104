import YM.MS.Arc.House
import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Estate
/-!
# House: forced fderiv holomorphic by polynomial-tempered bounds

Uniform on each closedBall admitted. Use only finite-dimensional external charts
 (suffices for projected result on all charts). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {E F I: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F][CompleteSpace F]
-- local growth round complex dimension
variable {f:ℂ→ E→ F}{D:Set ℂ}{c:ℂ}{R:ℝ}
-- uniform approximate
-- directional hol
open ContinuousLinearMap
variable {K Q: Type}
end YM.MS.Arc
