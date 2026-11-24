import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open Metric
variable {F:Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
abbrev Forest (D:Set ℂ)(f:ℂ→F): Prop:= ∀ z∈D,DifferentiableAt ℂ f z
end YM.MS.Arc
