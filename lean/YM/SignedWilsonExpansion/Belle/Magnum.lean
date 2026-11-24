import YM.SignedWilsonExpansion.Belle.Buffet
/-! Seven face polynomial decomposition AFTER original exterior integral. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SignedWilsonExpansion.Belle.Magnum
open FVA2 FVA2.Dframe FVA2.Scale Dancer Dancer.Drawing Dancer.SeatsW
open Function Filter Asymptotics MeasureTheory Set XSpace XSpace.Structure1 Normalize
open MS MS.Menus MS.Puff MS.High MS.Land MS.Native MS.Fleet Maxwell Maxwell.Free Maxwell.Wick
open WilsonCoeffUV.Mer.Xa MarqueQ Crops PorchK PowerSeries Lesson Path Rose Commission
open Buffet
open scoped Topology BigOperators Classical
variable (x t r: Rose.Badge→ℂ)
def peak (s:Finset (Fin 3)):= x s - t s
-- sign choice: carries negative direction, t=patchInsertion
-- carries FIRST insertion and builds explicit list of remaining products via summands evaluated after pricing, not conditional cumulant
abbrev effect : ℂ := -( t Finset.univ ) + t {0,1} * x {2}+t {0,2}*x {1}+ t {1,2}*x {0} + (x {0,1}-2*x {0}*x {1})*t {2}+(x {0,2}-2*x {0}*x {2})*t {1}+(x {1,2}-2*x {1}*x {2})*t {0}
abbrev higherEffect : ℂ:= -( t {0,1}*t {2} + t {0,2}*t {1}+ t {1,2}*t {0}) + 2 * (x {0}*t {1}*t {2} + t {0}*x {1}*t {2} + t {0}*t {1}*x {2} - t {0}*t {1}* t {2})
lemma tail : cumul ( x-t )=cumul x+ effect x t+higherEffect x t:=by unfold cumul effect higherEffect; simp only [ Pi.sub_apply ]; ring
abbrev sums : ℂ:= effect ( x-t ) (-r)+higherEffect ( x-t ) (-r)
theorem cumul_heat : cumul ( x-t+r )=cumul x + effect x t + higherEffect x t + sums x t r:=by
   calc _=cumul (x-t - (-r) ):=by rw [sub_neg_eq_add]
        _=_:=by rw [tail,tail]; unfold sums; abel
end YM.SignedWilsonExpansion.Belle.Magnum
