import YM.MS.Motif.Binary
import YM.MS.Image.Globe
/-!
# Row-spacetime odd variations by field replacement with given vector: no derivatives of vector at symbol momentum, no coincidence loop

Stencils of all finite rank. Ward-to-local construction.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
-- channel and P independent
variable {A P R B:Type}[CommRing R][AddCommGroup P] {p:Sector A}{b c:Bool}{u f g:Row A P R}{i:A}
local infixl:67 "⋄"=> product (field p)
-- ordered replacement any spatial derivatives; multiply only on left


end YM.MS.Motif
