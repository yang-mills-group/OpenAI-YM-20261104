import YM.MS.Arts.Meter
import YM.MS.Arts.Step

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux
open Momentum Landau
open scoped Topology ContDiff
variable {G:Gauge} {m:ℕ} {F:Mob G} {U:Rip G}
variable {s t:Bool} {c d:G.ColorIndex} {x:SectorP m} {l: Legs (Shore G m)}
def token (U:Rip G)(F:Mob G)(s t:Bool)(c d:G.ColorIndex)(x:SectorP m)(l:Legs (Shore G m)): ℂ:= fleck (Nat.le_succ m) U F (step (Nat.lt_succ_self m)) (step (Nat.lt_succ_self m)) s t c d x l
def yeast (U:Rip G)(F:Mob G)(x:SectorP m)(l:Legs (Shore G m)): ℂ:= ∑ s:Bool,∑ c:G.ColorIndex,∑ t:Bool,∑ d:G.ColorIndex,token U F s t c d x l
def Wtr (z:ℂ)(U:Rip G)(F: Mob G)(x:SectorP m): Rack G m:= trc (U m) x (F m)+(2*(z-m)) • yeast U F x -- check scalar parse
end YM.MS.Arts
