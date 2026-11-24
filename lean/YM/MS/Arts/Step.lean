import YM.MS.Arts.Par

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open Momentum
variable {m n:ℕ}
variable (h:m≤n)
abbrev step (hp:m<n) : Apart m n:= ⟨0,by unfold GlyphA; omega⟩
def hatch (h:m<n): L n:= aside h.le (step h)
end YM.MS.Arts
