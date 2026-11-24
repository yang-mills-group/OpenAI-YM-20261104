import YM.MS.Arts.Range

set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Flux Landau Arts
open scoped Topology ContDiff
variable {G : Gauge}
def mend (U: ℝ→Mob G)(x:ℝ): Mob G:= fun m l=> ∫ t in Iic x,U t m l
end YM.MS.Hem.Mell
