import YM.OPE.Compatible.Karls.Bruno
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
open Filter Finset
open Quit.PriceZ
lemma powerSun (L:E→L[ℝ] E)(B:Dice (KernP L q m))(x y:KernP L q m):Sky (q*q) (m+m) fun i=>B ((portC L q m^i) x) ((portC L q m^i) y):=by refine skyStem (m+m) (portC L q m) B m m le_rfl x y ?_ ?_ <;> rw [honestC]; all_goals rfl
end YM.OPE.Hark
