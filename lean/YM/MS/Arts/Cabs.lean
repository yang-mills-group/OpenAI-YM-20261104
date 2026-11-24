import YM.MS.Arts.Par

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open Momentum
variable {A B:Type} [Fintype A] [Fintype B] {m n:ℕ}
def lookG (f:A→B): Momentum B→L[ℝ] Momentum A:= ContinuousLinearMap.pi fun i:A=> ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:B=>ℝ) (f i)
variable (h:m≤n)
abbrev Left (h:m≤n):= sendB (rises h)
abbrev Cl (h:m≤n) := lookG (rises h)
end YM.MS.Arts
