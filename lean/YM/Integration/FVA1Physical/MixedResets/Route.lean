import YM.Integration.FVA1Physical.MixedResets.Seam
import YM.Integration.FVA1Physical.MixedResets.VacuumCover
import YM.Integration.FVA1Physical.MixedResets.Reset
import YM.Integration.RunFormalChain
import YM.QuadraticLocal.Advent

/-!
# Path convention of the mixed prescription

All of `R`, the layout, its high extra vacuum order p₀, and its *formal* coupling
renormalizations can be specified without proposing an approximation to any marked
integral. Recursive step on model rows (with incoming packet decomposition fixed).
It is convenient to give the analytic model before and after the reparameterization.
Keep the same physical parameters (β of the actual path) at every evaluation and
in every mask of the true density. They are not inferred from the formal calibrator.

`Route.wilson` here is the COVER step; `Route.datum` & `Route.winding` serve as explicit
access to the exact finite-period comparison with the independent `LocalFormal` API
(in addition to assembling the cover result from that Fk on periods increasing in lattice units).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
namespace Route
open Filter Function Finset Lattice RG Wilson Marker Precision Tree Input
open Push Uniform Next.SectorChange
open Comparison.RG02
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn
open scoped Classical Topology BigOperators
open AllOrder.Floe.Step.PlanV Pressure Gauge
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat Legato ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero
open Integration

variable {G : Gauge} (R : Run G) {V : Type} [Fintype V] [DecidableEq V] {I : Marker.Census V} {U : Layout G}
    {ι α : Type} (N i n : ℕ)

/-- Calibrated physical *g*, not chosen from the estimate. -/
def coupling : ℝ := Coat.gStep (R.family.path.rep N n i).beta
/-- Report/stage. RG: i+1 to i. -/
abbrev step := R.family.path.levels.clock.op i n
/-- Same clipped kernel on this `Kin` on which the real density is represented. -/
def action := (R.family.path.rep N n i).path
def clip := (R.family.path.rep N n i).clip

variable {n i}
variable (p₀ : ℕ) (U : Layout G)
-- vacuum extra order (total bank cost)

set_option quotPrecheck false
local notation "Φ" j:max => R.family.side j n
local notation "C" => R.family.path.levels.clock.op i n
local notation "K" => RunFormalChain.fromRun R
local notation "W" => Step.tape p₀

def vacuum (r : ℕ) (z : rule (Coarse G) (R.family.side i n)) : ℂ :=
  coverAction (Route.step R i n).patch (C).kernel R.metals.O (Route.action R N (i+1) n)
    (Route.clip R N (i+1) n) U W p₀ r z

variable {A : Passport (R.family.side (i+1) n) V}
    (M : ι → Row A I G α)
/-- Pre-reset coupling convention. -/
def wilson (p : ℕ) := coverStep (Route.step R i n) R.metals.O
  (Route.action R N (i+1) n) (Route.clip R N (i+1) n) U (Step.tape p₀) M p

/-- Exactly that same comparison with both coupling and field reexpressed. -/
def reexpress (p : ℕ) (Q : Adjacent.Caliber) : ℕ → α → rule (Coarse G) (R.family.side i n) → Poly I :=
  combineReset Q p₀ p (Route.wilson R N p₀ U M p)

variable (grades : V → ℕ) (F : Forest ((Route.step R i n).ratio)) (t : (Route.step R i n).Choices)
  (cut : i < N) (χ : α) (z : rule (Coarse G) (R.family.side i n))
  (u : Club M)
set_option quotPrecheck false
local notation "ℓ" => tint G (Exterior.Body 1 (R.family.side i n)) (exteriorL G (R.family.side i n) z)

def datum : Integration.LocalFormal.Datum R.family I :=
  ⟨N,n,i,cut,F,t, colorsOf M U W grades χ, ℓ⟩

def winding (p r : ℕ) (u : Club M) : Poly I :=
  let L := R.family.side i n
  ScatterR.unitTerm M U W ((RunFormalChain.fromRun R).step N i n cut) F t
      (tint G (Exterior.Body 1 L) (exteriorL G L z))
      (fun i => (M i).paint χ) r p u -
    clubOutput C R.metals.O (Route.action R N (i+1) n) (Route.clip R N (i+1) n) U W M p r χ z u

-- symbol equivalence `localFormal` per projected ordinary chart and on path `root`. Expose gaussian when compiled.
omit [Fintype V] in
lemma raw_action_inv_g (A' : Layout G) (g : ℝ) (hg : g ≠ 0)
    (scalar : ℝ) (x : Config G (R.family.side (i+1) n)) :
    Integral.weight g scalar x (colorsOf M A' W grades χ)
      (Route.clip R N (i+1) n) (Route.action R N (i+1) n) =
    Real.exp (scalar - Integral.temperature g * Floe.audition (Route.action R N (i+1) n)
        (Route.clip R N (i+1) n) A' W g x) :=
  Faith.Costume.native (Route.action R N (i+1) n) (Route.clip R N (i+1) n) W A'
    (colorsOf M A' W grades χ) g hg scalar x
end Route
end YM.Integration.FVA1Physical.MixedResets
