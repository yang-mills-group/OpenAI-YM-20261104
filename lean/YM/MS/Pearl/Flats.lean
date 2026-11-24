import YM.MS.Pearl.Broach
import YM.MS.Shine.Mud

set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Flux Landau Arts Arc Wire Rock Alps _root_.YM.MS.Shine Hem Mell
open scoped Topology ContDiff Interval
variable {G:Gauge} {h ℓ:ℕ}
abbrev Coat (G:Gauge):=ℂ→Mob G
abbrev Flats (G:Gauge):= ℕ →₀ Coat G
def Parade (F:Flats G)(h:ℕ)(y s:ℝ): Coat G:= fun i=> F.sum (fun ℓ F=> hikeP i h ℓ y s (F i))
variable {F:Flats G}
abbrev Rent (F:Flats G)(j:ℕ): Prop:= ∀ i, altitude j ( F i)
end YM.MS.Pearl
