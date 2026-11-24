import YM.FVA2.Position.Browse
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Position.Lantern
/-!
# Multiplicative extension of the Jrad convention (`OpenAxis.Ramp` in `Echo.lean`)

Here prepare a polynomial in the full curvature rank assignments before color averaging.
`ramp_rank`, `seed_p`, `chooses` are checks with the actual `unavg` mark-column data.
In `Position/Table.lean`, use this for the **specific** continuation prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.OpenAxis
open Function Set Filter Finset
open MS MS.Plane MS.Koszul MS.Motif MS.Arts MS.Garment MS.Halo MS.Mach MS.High
open MS.Landau MS.Book MS.Color MS.Lifting
open Analysis Tensor Maxwell Labels MS.Theater
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{G:Gauge}{m n h:ℕ}{x:E4}{z:ℂ} {a b c:Axis}
local notation "Lℂ"=> asC G h
local notation "Φ"=> Seed G
-- before averaging over G, rows real (only real-linear choices from curvature words).
-- Real span. See `ramp_rank`. No positivity precondition to use it.
-- prove general with appended axes for convoke step.
-- axes reversed but identical factors commute before; prove.

-- polynomials embed. Dark gives honest signs in Wick algebra. show stays in word span.

local notation "T"=> seed G
local notation "κ"=> Ramp G

variable {f p:Pol G}{n k:ℕ}
-- For real polynomial rows, can use real coefficients in the span proof.
end YM.FVA2.Position.OpenAxis
