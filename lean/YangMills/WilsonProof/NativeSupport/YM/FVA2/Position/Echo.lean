import YM.FVA2.Position.Echo
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Press.Deck
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Pick
/-!
# Open-index continuation of exactly the radial-polynomial lift before pole subtraction

For exact bare-regulator comparison and matching. Don't equate different positive-order covariantizations.
This map for a `Taylor` linear coordinate uses the radial curvature polynomial, before any dimension-dependent rewrites, on the insertible four axes
in the supplied MS continuum calculus. g is `z : ℂ`; includes z in curvature and covariant
derivatives, so the mark is taken *after* connection rescaling. Step now:
it defines a map on Taylor covectors themselves, not multivalued from tensor decomposition.
Parity, signed rotations and physical Booked construction later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.OpenAxis
open Function Set Filter Finset
open MS MS.Plane MS.Koszul MS.Motif MS.Arts MS.Garment MS.Halo MS.Mach MS.High
open MS.Landau MS.Book
open Analysis Tensor Maxwell Labels MS.Theater
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{G:Gauge}{m n h:ℕ}{x:E4}{z:ℂ} {a b c:Axis}



-- functions of spacetime are exactly homogeneous Taylor. Prove *any* linear reading on
-- Mield before evaluating continuation or applying identities.


local notation "ρ" => Complex.reCLM.toLinearMap
local notation "μ" => Complex.imCLM.toLinearMap
local notation "Φ" => Witness G h
-- real Taylor covector, then complex convention. z in the MS formal-coupling prescription.
local notation "☼"=> asC G h

end YM.FVA2.Position.OpenAxis
