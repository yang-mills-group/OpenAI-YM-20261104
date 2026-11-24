import YM.MS.Graphical.PinScale

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Flux Landau Arts Arc Wire Rock Alps
open _root_.YM.MS.Shine Hem Mell Pearl
open scoped Topology ContDiff Interval
variable {t w: ℝ} {m: ℕ} {G: Gauge}
variable {F: Schedule G} {z: ℂ}
/-- Specialize, always **after** collecting the counterterm graphs. Pointwise limit as `z`
tends to zero, through nonzero values. See `Countered.limit`. -/
def regularPart (F : Schedule G) (t : ℝ) : Mob G := fun m w=> limUnder dotty (fun z=> F t z m w)
end YM.MS.Graphical
