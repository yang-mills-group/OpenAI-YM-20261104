import YM.MS.Alps.Easy
import YM.MS.Hem.Choose
import YM.MS.Shine.Pick

set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Classical
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Flux Landau Arts Arc Wire Rock Alps _root_.YM.MS.Shine Hem Mell
open scoped Topology ContDiff Interval
variable {G:Gauge} {x:ℂ} {n ℓ:ℕ} {h:ℕ}
variable {f: ℂ→ Mob G}
open Classical in
/-- `η`-jet Taylor selected even on $f_z$ with arbitrary formal value at zero in expression -/
def ruby (f:ℂ→Mob G)(n:ℕ): Mob G := if h:Live f then choose (given h n) else 0
def weight (x:ℂ)(ℓ:ℕ)(y:ℝ): ℂ:=amount (toll x ℓ) y
def hikeP (x:ℂ)(h ℓ:ℕ)(y t:ℝ)(f:Mob G): Mob G:= weight x ℓ y • plow (vamp x h ℓ) t f
end YM.MS.Pearl
