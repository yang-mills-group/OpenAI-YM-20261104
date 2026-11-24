import YM.MS.Arts.Range
import YM.MS.RayRules

set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem
open Set Filter Function Finset MeasureTheory Metric
open Plane Koszul Flux Landau Arts
open scoped Topology ContDiff
variable {G:Gauge} {F:Mob G}
def Tad (F:Mob G)(e:ℕ): Mob G:= fun _=> Plane.skin wfield e (F _)
end YM.MS.Hem
