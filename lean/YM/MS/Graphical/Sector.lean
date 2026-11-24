import YM.MS.Alps.Easy
import YM.MS.Hem.Aryl
import YM.MS.Hem.Choose

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set (Iic)
open Filter Function Finset MeasureTheory
open Plane Koszul Flux Landau Arts Alps
open Hem Mell
open scoped Topology ContDiff Interval
variable {G: Gauge} {m k h: ℕ} {F: Mob G} {z x: ℂ}
/-- Integrand : in log length `t`, with the common IR convention using actual
momenta (scale-one argument of `F` gets the **scaled** external momenta). -/
def scalingShell (x : ℂ) (F : Mob G) (t : ℝ) : Mob G :=
  fun _ w => Complex.exp ((t : ℂ) * (x + (mass w : ℂ))) * F _ (sr t w)
/-- Analytic endpoint integral of the indicated Taylor orders below the cut.
This is *added*. Don't interpret this evaluation at a resonant exponent. -/
def analyticTail (k : ℕ) (x : ℂ) (cut : ℝ) (F : Mob G) : Mob G :=
  ∑ j ∈ range k, (Alps.amount (x + j) cut / (x + j)) • Tad F j
def cutIntegral (loops h : ℕ) (s cut : ℝ) (z : ℂ) (F : Mob G) : Mob G := fun m w =>
  (∫ t in cut..s, scalingShell (vamp z h loops) F t m w) +
  if loops = 0 then 0 else analyticTail (h + 1) (vamp z h loops) cut F m w
/-- Sector prescription at the largest remaining log length integration, holding
`s` (common IR log length) **fixed**. For hypotheses giving this limit, see `removal`. -/
def scaleIntegral (loops h : ℕ) (s : ℝ) (z : ℂ) (F : Mob G) : Mob G := fun m w =>
  limUnder atBot (fun cut : ℝ => cutIntegral loops h s cut z F m w)
end YM.MS.Graphical
