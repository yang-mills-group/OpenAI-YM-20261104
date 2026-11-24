import YM.QuadraticLocal.Class.Augur
import YM.QuadraticLocal.Class.Exposure

/-!
# Choosing a run for the local comparison

For a gauge group satisfying `G.Simple` and a prescribed positive clock penalty,
`Checkpoint4.setup` applies `Shuttle.posts` to the schedule
`MintClock.splits`. It selects one run, its roots and table, and the books
and forecast used by the comparison. On that run it obtains the stage for
`Tracks.readings`, the prescribed penalty, and the `Warm`, `Quarterly` and
`Reach` conditions.

The marked step and budget estimates are separate statements on the
trajectory and its input data. For example, `Eon.constitutes` uses the
chosen path and its representations. `Eon.estate` gives the corresponding
budget under its bounds on the loss exponents.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Checkpoint4
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat ConnectedActivityE6 Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open AllOrder AllOrder.Burn MintClock
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Asymptotics
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open Input Org Wilson ThroughLaunch PriceCompiler Legato Legato.VowsR
open Advent Advent.Sycamore
variable {G: Gauge} (g:G.Simple) (β:ℝ)
local notation "φ"=> MintClock.splits
set_option quotPrecheck false
local notation "D*"=> ( VowsR.probe G φ )
include g
theorem setup (hp:0<β): ∃ (R:Run G)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q φ)(Qa:Mentor.Forecast D R.rolls Q φ Q0), WithStage R.metals.p Tracks.readings ∧ R.family.path.levels.clock.kernel.penalty= β∧ Spill.Raffle.Warm G D R.alloy.delay φ∧ Oak.Tutoring.Quarterly R D Q ( VowsR.probe G MintClock.splits ) Q0 Qa ∧ Spill.Walking.Reach G D R.alloy.delay φ:= Shuttle.posts g _ β hp le_rfl
end YM.QuadraticLocal.Checkpoint4
open YM.QuadraticLocal.Advent.Sycamore
