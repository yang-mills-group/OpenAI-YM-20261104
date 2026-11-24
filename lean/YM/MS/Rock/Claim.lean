import YM.MS.Arc.Estate
import YM.MS.Rock.Fell

set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux
open Momentum Landau Arts Arc Wire
open scoped Topology ContDiff
open Metric
variable {G:Gauge} {I:Type} {z:UScale I} {f:ℂ→Mob G}
variable {D:Set ℂ}
abbrev hill (D:Set ℂ)(f:ℂ→Mob G): Prop:=∀ i, ∀ w:Legs (Shore G i), Forest D fun z=> f z i w
structure Hol (D:Set ℂ)(f:ℂ→ Mob G): Prop where
   price c R: 0<R→ closedBall c R⊆D → fell 0 (fun _:closedBall c R=>1) (fun i=> f i)
   top: hill D f
end YM.MS.Rock
