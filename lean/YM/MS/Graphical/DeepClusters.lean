import YM.MS.Graphical.IntegratePins
import YM.MS.Graphical.Registered

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Flux Landau Arts Arc Wire Rock Path Alps
open _root_.YM.MS.Shine Hem Mell Pearl Train
open scoped Topology ContDiff Interval
variable {n: ℕ} {G: Gauge}
variable {F: Schedule G}
def runCloses (y : ℝ) (F : Schedule G) (n : ℕ) := (integratePins ∘ closeAt y)^[n] (integratePins F)
def pinTower (y : ℝ) (F : Schedule G) (n : ℕ) := ∑ i∈ Finset.range (n+1), runCloses y F i
end YM.MS.Graphical
