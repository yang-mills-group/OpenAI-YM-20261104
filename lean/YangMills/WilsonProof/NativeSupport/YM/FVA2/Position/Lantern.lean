import YM.FVA2.Position.Lantern
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Position.Echo
/-!
# Connection of `Ray` to rank-one datum of MS `Ramp`

`prong_lit`, `ramps_real`: at zero coupling, fixed physical dimension,
interpret as the `RowLeg`. These help build the nonlinear prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.OpenAxis
open Function Set Filter Finset
open MS MS.Plane MS.Koszul MS.Motif MS.Arts MS.Garment MS.Halo MS.Mach MS.High
open MS.Landau MS.Landau.Detect MS.Book MS.Momentum
open Analysis Tensor Maxwell Labels MS.Theater
open InnerProductSpace
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{G:Gauge}{m n h:ℕ}{x:E4}{z:ℂ} {a b c:Axis} {p:FourP}
local notation "µ"=> Theater.carve
local notation "↓"=> Tensor.diagonal
-- ordinary curvature formula vs projection to radial. Holds on *unrestricted* Feet.


local notation "☼"=> asC

end YM.FVA2.Position.OpenAxis
