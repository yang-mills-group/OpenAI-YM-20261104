import YM.MS.Arts.Range

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Flux Landau Arts
open scoped Topology ContDiff
variable {G:Gauge} {n:ℕ}
abbrev Chan (G:Gauge)(n:ℕ):= Option (Arts.L n) × G.ColorIndex
def onX (t:Bool)(p:Chan G n): Cfield G n := ((p.1,t),p.2)
def mote (a:Cfield G n): Chan G n:= (a.1.1,a.2)
abbrev phase (p:Chan G n): ℂ:= if p.1=none then -1 else 1 -- keyword none use none.
lemma onXC (p q:Chan G n)(b:Bool): onX b p=onX b q↔p=q:= by constructor; exact fun ht=>congr_arg mote ht; intro h; rw [h]
end YM.MS.Motif
