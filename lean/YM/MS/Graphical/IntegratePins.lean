import YM.MS.Graphical.PinScale
import YM.MS.Hem.Glory

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Flux Landau Arts Arc Wire Rock Alps
open _root_.YM.MS.Shine Hem Mell Pearl
open scoped Topology ContDiff Interval
variable {G : Gauge}
/-- Integrate the scale force for a genuine multi-pin. No extra subtraction
hidden in this integral. `mend` is the length integral from log time −∞ through upper t
(here verify by UV limit at fixed IR). -/
def integratePins (F : Schedule G) : Schedule G := fun t z=> mend (fun x=> F x z) t
end YM.MS.Graphical
