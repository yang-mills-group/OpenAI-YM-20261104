import YM.MS.Graphical.Sector
import YM.MS.Pearl.Flats
import YM.MS.Shine.Purity

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Filter Set Function Finset MeasureTheory
open Plane Koszul Flux Landau Arts Arc Wire Rock Alps
open _root_.YM.MS.Shine Hem Mell Pearl
open scoped Topology ContDiff Interval Classical
variable {G: Gauge} {V X: Flats G} {n h ℓ: ℕ} {z: ℂ} {f: Coat G}
/-- Integral of a scale sector node. `V` is the graph/forest sum with the
largest-scale edge marked with shell at scale 1, still to integrate d(log length).
Normalized to upper length 1, to be read out with `hikeP`/`Parade`. -/
def integrateShell (h : ℕ) (V : Flats G) : Flats G :=
  V.sum fun ℓ f => Finsupp.single ℓ (fun z => scaleIntegral ℓ h 0 z (f z))
/-- Choose a common upper bound on pole order across pages (junk off domain);
NOT extracted from any MS data. -/
def poleBound (X : Flats G) := if h : ∃ n, Rent X n then Nat.find h else 0
/-- Counterterm sign included. For transparency evaluate a single ordinary
Laurent PP on the **summed** sector, multiplying by z^poleBound before
reading Taylor coefficients. -/
def selectCT (h : ℕ) (X : Flats G) : Coat G :=
  -(∑ i ∈ range (poleBound X), Ice (poleBound X-i) (ruby (paid (poleBound X) (Parade X h 0 0)) i))
structure SectorFamily (G : Gauge) where
  pages : Flats G
  ct : Coat G
  deriving Inhabited
/-- Renormalized history through this node. `V` already includes the child pole
insertions with their signs. The overall pole part subtracted off is formed from
the integrated `V`. -/
def integrateRen (h : ℕ) (V : Flats G) : SectorFamily G :=
  let X := integrateShell h V
  let W := selectCT h X
  ⟨X + Finsupp.single 0 W, W⟩
end YM.MS.Graphical
