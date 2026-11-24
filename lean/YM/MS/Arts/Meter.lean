import YM.MS.Arts.Range
import YM.MS.Arts.Rare

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux
open Momentum Landau
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {m n:ℕ} {F:Mob G} {U:Rip G}
variable (h:m≤n)
variable {h}
variable {i j: Apart m n} {s t:Bool} {c d:G.ColorIndex} {x:SectorP m} {l: Legs (Shore G m)}
def fleck (h:m≤n)(U:Rip G)(F:Mob G)(i j:Apart m n)(s t:Bool)(c d:G.ColorIndex)(x: SectorP m)(l:Legs (Shore G m)): ℂ:=
    U n (vleg s (aside h i) c) (vleg t (aside h j) d) (Left h x)*F n ((vleg s (aside h i) c,Left h x):: (vleg t (aside h j) d, - Left h x)::lift h l)
end YM.MS.Arts
