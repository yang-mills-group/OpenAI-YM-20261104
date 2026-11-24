import YM.MS.Local.Differential
import YM.MS.Local.Number
import YM.MS.Local.Finite
import YM.MS.Local.ExactSpan
import YM.MS.Local.String
import YM.MS.Local.Monomial
import YM.MS.Local.Tile
import YM.MS.Roles
import YangMills.WilsonProof.NativeSupport.YM.MS.Color.Components
import YM.MS.Class.Cube
/-!
# Local one-slot arrows in free charge, parity and Hessian relations
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MatrixLet
open Landau Detect Detect.Mark
open Complex (I)
open scoped Topology ContDiff
variable {G : Gauge}
-- on one
variable (f : Grade G) (i j k :CI G) (a:Axis) (p:FourP)

end YM.MS.Local.BV
