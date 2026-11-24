import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import YM.MS.Pearl.Broach

set_option autoImplicit false
noncomputable section
namespace YM.MS.Train
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Flux Landau Arts Arc Wire Rock Alps _root_.YM.MS.Shine Hem Mell Pearl
open scoped Topology ContDiff Interval
def room : ℝ:= ((2*π:ℝ)^4)⁻¹
def feeD (z:ℂ): ℂ:= (room:ℂ)* Complex.exp (z*((Real.log π-2*Real.log (2*π):ℝ):ℂ)) / Complex.Gamma (z+1)
def tenorK (z:ℂ)(y:ℝ): ℂ:= weight z 1 y * feeD z
end YM.MS.Train
