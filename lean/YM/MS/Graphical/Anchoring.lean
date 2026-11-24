import YM.MS.Arts.Range
import YM.MS.Tone.Beat

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Flux Landau Arts
open scoped Topology ContDiff
variable {G: Gauge}
variable {F H: Mob G} {m: ℕ} {q: ℤ}
def phase (m : ℕ) (z : Tone.QP) (q : SectorP m) := Tone.bill z (Cl (Nat.zero_le m) q)
def bring (z : Tone.QP) (F : Mob G) : Mob G := fun m l=> phase m z (net l)*F m l
def shuffleRows (F H : Mob G) : Mob G := fun _ => product (field Landau.parity) (F _) (H _)
end YM.MS.Graphical
