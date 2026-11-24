import YM.MS.Graphical.Anchoring
import YM.MS.Graphical.Lines

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Flux Landau Arts Arc Wire Rock Path Alps
open _root_.YM.MS.Shine Hem Mell Pearl Train
open scoped Topology ContDiff
variable {G: Gauge} {F H: Mob G}
variable {U: Rip G} {z: ℂ}
def wickJoin (u : Tone.QP) (U : Rip G) (z : ℂ) (y : ℝ) (F H : Mob G) : Mob G :=
  radialClose U z y (shuffleRows (bring u F) H) -
    shuffleRows (radialClose U z y (bring u F)) H - shuffleRows (bring u F) (radialClose U z y H)
end YM.MS.Graphical
