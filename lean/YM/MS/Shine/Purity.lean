import YM.MS.Arts.Range

set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric
open Plane Koszul Flux Landau Arts
open scoped Topology ContDiff
variable {G:Gauge} {F:Mob G} {m:ℕ}
def Ice (m:ℕ)(F:Mob G)(i:ℂ): Mob G:= i⁻¹^m • F
end YM.MS.Shine
