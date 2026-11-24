import YM.MS.Arts.Range
import YM.MS.Charted

set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux
open Momentum Landau Arts Wire
open scoped Topology ContDiff
abbrev Touch (G:Gauge)(m:ℕ)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] := Wire (Cfield G m) E (SectorP m)
end YM.MS.Rock
