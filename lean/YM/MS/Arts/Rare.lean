import YM.MS.Landau

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux
open Momentum Landau
open scoped Topology ContDiff InnerProductSpace
variable {C A:Type} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
def vleg (s:Bool)(p:A)(c:C): Leg A C:= ((some p,s),c)
end YM.MS.Arts
