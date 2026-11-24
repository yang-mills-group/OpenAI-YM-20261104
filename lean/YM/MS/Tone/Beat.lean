import YM.MS.SineMomentum

set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone
open Function Filter Set Finset
open Momentum Real
open Complex (I)
open scoped Topology ContDiff
abbrev QP := Momentum Axis
def bill (p q:QP) : ℂ := Complex.exp (Complex.I * pairing p q)
end YM.MS.Tone
