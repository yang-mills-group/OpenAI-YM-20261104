import YM.MS.Arc.Terrain
import YM.MS.Arts.Range
import YM.MS.Charted

set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux
open Momentum Landau Arts Arc Wire
open scoped Topology ContDiff
variable {G : Gauge} {I : Type}

def fell (z:UScale I)(a:I→ℝ)(f:I→Mob G): Prop:= ∀ m (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E], ∀ w:Wire (Cfield G m) E (SectorP m), veg z (fun i=>fieldVal (f i m) w) a
end YM.MS.Rock
