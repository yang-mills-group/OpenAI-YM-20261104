import YM.MS.Tone.Beat

set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Tone Momentum
open scoped Topology ContDiff Interval
variable {I W:Type} [LinearOrder W]
abbrev Position (W I:Type):= W→I→QP
def rootX (x:Position W I)(s:Finset W) : I→ QP := if p:s.Nonempty then x ( s.min' p ) else 0
def picks (s:Finset W): Finset (Finset W):= s.powerset.filter (fun k=> k.Nonempty ∧ if h:s.Nonempty then s.min' h∉ k else False)
end YM.MS.Rake
