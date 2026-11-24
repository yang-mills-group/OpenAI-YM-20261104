import YM.MS.Graphical.NextWick
import YM.MS.Graphical.PinScale

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Flux Landau Arts Arc Wire Rock Path Alps
open _root_.YM.MS.Shine Hem Mell Pearl Train
open scoped Topology ContDiff Interval
variable {t: ℝ} {G: Gauge} {x: Tone.QP}
variable {F H: Schedule G} {z: ℂ}
def closeAt (y : ℝ) (F : Schedule G) : Schedule G:= fun t z=> radialClose (halfD t) z y (F t z)
def treeAt (F H : Schedule G) : Schedule G:= fun t z=> bridging t (F t z) (H t z)
def joinAt (x : Tone.QP) (y : ℝ) (F H : Schedule G) : Schedule G:= fun t z=> wickJoin x (halfD t) z y (F t z) (H t z)
end YM.MS.Graphical
