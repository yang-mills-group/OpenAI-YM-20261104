import YM.MS.Shine.Heart

set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Flux Landau Arts Arc Wire Rock
open scoped Topology ContDiff
variable {G:Gauge} {x:ℂ→ℂ} {f:ℂ→ Mob G} {n:ℕ}
def paid (j:ℕ)(f:ℂ→Mob G): ℂ→ Mob G:= fun x=> x^j • f x
def altitude (n:ℕ)(f:ℂ→Mob G): Prop:= Live (paid n f)
end YM.MS.Shine
