import YM.Integration.FVA1Physical.MixedResets.Bilateral
import YM.QuadraticLocal.Tariff.Labeling

/-!
# qlocal at the House schedule: single FULL conditional step

General e version too. Models identified by the exact COVER coefficients
(not requiring winding estimates to buy accuracy of a point reading). Formula,
vacuum subtraction, forced reserve and through-order high calibration all
on the chosen Run. For the general e call there is no claim of using the
re-expression produced here with another reset, or of any calibrated e↦β
policy compatible with the manuscript for every thermal input with this norm.
Also here does not treat separately a non-affine `e^natural`. Use the calibrated
version for iteration (CP5 on actual trajectory Ψ in this house).

This file does not purchase the schedule or even the calendar gate. Below on
application the SAME parameters and schedule choices get `Contacts` and ALSO
the continuation with `Agenda`; thus no need to sacrifice one to get the other.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open Pressure Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore QuadraticLocal.Syl
open Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree
open Oak
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m n i k N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) {Ψ : ∀ i, RG.Rep G (R.family.side i n)}
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  {φ : ℕ → ℕ} (clock : Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ clock)
  (hi : m ≤ i) (cut : i<N) (L : ∀ i, ∀ h:m ≤ i, i<N → Lesson (N:=N) R J D Q π Γ h)
  (U : RG.Rep G (R.family.side (i+1) n))
  (allowC μ : ℝ)
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "I" => R.alloy.B.a.clock.J i
local notation "I'" => R.alloy.B.a.clock.J (i+1)
attribute [local irreducible] Till.Tilt.sundry
local notation "C" => R.alloy.B.a.budget i
local notation "Fμ" => R.alloy.B.a.budget (i+1)
local notation "τ" => R.family.path.levels.clock.op i n
local notation "µ" => (τ).ratio
local notation "p₀" => (Burn.horizon k+2)
local notation "g" => Coat.gStep U.beta
local notation "LL" => (L i hi cut)

variable (school : School k)
  (hp : RG.Shoot.Lives (WheelP.neutral R.alloy).bake N (i+1) n U)
  (e : ℝ) (seed : Burn.Seed U (WheelP.M0 k 0 (R.alloy.B.a.budget (i+1)) (π (i+1)) U.beta))
  (hw : U.beta ∈ RG.Shoot.band R.alloy.B.a (i+1))
  (hW : e ≤ allowC * (Coat.gStep U.beta)^((school.order:ℝ)+1-μ))
  (hE : Burn.Candor (R.alloy.B.a.budget (i+1)) U.activities (Set.range seed.model) (Burn.silver ( R.alloy.B.a.clock.hatBeta (i+1))) e)
local notation "p" => school.order
local notation "horizon" => school.horizon
local notation "tall" => school.pieces
local notation "cap" => (School.room school (PriceCompiler.step_paid (σ) i) (J.trans (R.alloy.B.a.fits.mono hi)))
variable {Θ ι ιw : Type} [Fintype Θ] [DecidableEq Θ] {R₀ : Marker.Census Θ}
  (o : Earn.Passport (R.family.side (i+1) n) Θ) {X : Θ → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
  (allow : ∀ i, Set (X i)) (kills : ∀ i, Submodule ℝ (X i))
  (M : ι → Earn.Row o R₀ G (Affinity.Wallet allow)) (Z : Tint.Incoming o U (Affinity.Wallet allow) ιw R₀)
  (w : Θ → ℝ) (grades : Θ → ℕ) (e_E funds ηz : ℝ) (s : ℕ)
local notation "u" => (Poetry.Agenda.seed D φ (Burn.horizon k) I')
variable (F₁ : Tree.Forest (Route.step R i n).ratio)
  (Voter : Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) school.order school.pieces (School.room school (PriceCompiler.step_paid R.alloy.B.a i) (J.trans (R.alloy.B.a.fits.mono hi))).stage k (R.alloy.B.a.clock.J i))

variable [Countable ι] [Countable ιw] [Nonempty (Affinity.Wallet allow)]
include conc hw hW hE hp
local notation "pushable" => ( Locator.Contacts R D Q clock ahead allowC μ ηz s school m N π Γ Ψ J L )
-- Voters proofs of geometry are independent of any particular output. In
-- particular there does not need to be a choice of supporter from the hall for
-- this theorem. Optional use without passing F -- we also return the Calendar.
-- Include actual K conditional denominator at formal cover: use hall.coherence
-- to get VacuumStep (at *actual* Ψ calibration), and PinnedSeam if requested.

set_option maxHeartbeats 650000
lemma single_step
    (earned : Earn.Scene.Armada M w grades u funds p tall horizon) (table : Tableau kills allow M)
    (located : Affinity.Collared o.support allow kills U (remainderGallery U Z))
    (paid : Z.old.Paid w U.p.B U.p.supportExponent e_E) (forces : Z.hard.Paid w U.p.B U.p.supportExponent 1)
    (cap_cost : funds ≤ 1) (h : 0≤e_E) (h' : e_E ≤ 1) (calendar : pushable) :
    let voter := School.future school (PriceCompiler.step_paid (σ) i) (J.trans (R.alloy.B.a.fits.mono hi)) grades M earned
    ∃ (pre : Locator.Calendar R J D Q π Γ hi (L i hi cut) (U:=U) e F₁)
      (J' : Type) (_i : Countable J') (next : Tint.Incoming (o.coarser ((τ).ratio))
        (Locator.paneling R J D Q π Γ hi (L i hi cut) pre.listing pre.source U.beta pre.scalar)
        (Affinity.Wallet allow) J' R₀),
    Locator.Elementary.Newhall (n:=n) (U:=U) R J D Q π Γ Ψ clock ahead hi cut (L i hi cut) e seed p F₁ pre (cap) allow kills M Z w grades horizon voter e_E funds ηz s next Set.univ ∧
    Early R J D Q π Γ clock ahead hi (L i hi cut) U cap e o allow kills M Z w grades p horizon e_E funds ηz s F₁ voter pre next := by
  intro voter
  obtain ⟨pre,hp1⟩ := calendar.calls i hi cut U F₁ e seed hp hw hW hE
  obtain ⟨vv,J',hs,next,hall⟩ := hp1.palace.gets Θ ι ιw R₀ o w X allow kills M Z grades e_E funds earned table located.lamps located.hard Set.univ
    (Lamps.loan_monotone _ paid h') (Deletion.owed _ _ paid) forces cap_cost h h'
  letI := hs
  refine ⟨pre,J',hs,next,hall,?_⟩
  exact pre_price R J D Q π Γ conc clock ahead hi cut LL U cap hp e seed o allow kills M Z w grades p horizon e_E funds ηz s F₁ voter pre next hall earned paid forces
end YM.Integration.FVA1Physical.MixedResets
