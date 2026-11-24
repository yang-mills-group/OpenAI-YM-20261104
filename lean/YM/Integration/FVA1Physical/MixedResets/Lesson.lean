import YM.Integration.FVA1Physical.MixedResets.Route
import YM.QuadraticLocal.Union.Step

/-!
# Exact cover model at a step of the actual history

The step used by the multi-mark push is an Oak.Lesson. Every such press runs the cover
version of `LocalFormal`, not a new current-scale forecast. Importantly, its choice of
analytic stencil/decomposition is part of this prescription: all the clocks/ledger proofs and
the analytic painter depend on vacuum programs & input models, *not* on marked remainders or
future receipt choices. All coupling-reset powers are at fixed p before actually putting those
models on the outgoing re-expression.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset MeasureTheory Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent
open Comparison.RG02 Further.PhysicalPeriodLimitF933
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m n i k N : ℕ}
variable (pay : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : pay.Tab R.rolls)
  (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
  (hi : m ≤ i) (L : Oak.Lesson (N:=N) R J pay Q π Γ hi)
  {Ψ : ∀ i, RG.Rep G (R.family.side i n)}
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ) (cut : i < N)
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "xStage" => R.alloy.B.a.clock.J (i+1)
local notation "yStage" => R.alloy.B.a.clock.J i
local notation "Y" => (RunFormalChain.fromRun R)
local notation "C" => Route.step R i n
local notation "p₀" => (Burn.horizon k+2)
local notation "T" => Step.tape p₀

include cut L
lemma lesson_action : Route.action R N (i+1) n = L.entry.self.north :=
  ((Y).selected N n (i+1) cut).trans L.studied.books.north.symm

omit L
lemma lesson_clip : Route.clip R N (i+1) n = (R.metals.p.profile (R.alloy.B.a.clock.J (i+1))).clip :=
  ((Y).clips N n (i+1) cut).trans (congr_arg RG.Stage.clip (params_eq R.alloy.B.valid _))

omit cut in
lemma lesson_patch : (Route.step R i n).patch = Mural.sheet R.metals.p R.rolls ( (σ).clock.adm (i+1) ) :=
  Plateau.Line.patch_here R.alloy ((R.alloy.B.a.S.oneStep i n).exact_size)

include conc L
lemma lesson_admitted : Bid.Larger (G:=G) (Route.step R i n) :=
  (Oak.agrees R J pay Q π Γ Ψ conc hi cut L).some.clock.laws.data.room.larger

section
variable {φ : ℕ → ℕ}
variable (clock : QuadraticLocal.Mentor.Offices.Books pay R.rolls Q φ)
  (capacity : QuadraticLocal.Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  {V α ι : Type} [Fintype V] [DecidableEq V] {I : Marker.Census V}
  {A : Passport (R.family.side (i+1) n) V} (M : ι → Row A I G α)
  {p : ℕ} (v : Cruise.Voter M
    (Poetry.Agenda.seed pay φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) p capacity.count capacity.stage k (R.alloy.B.a.clock.J i))
local notation "𝒮" => Cruise.publish pay R.rolls Q R.alloy φ clock capacity
    (Oak.era R J pay Q π Γ hi capacity L) ((σ).S.oneStep i n).exact_size M p v L.entry
local notation "g" => (Route.action R N (i+1) n)
local notation "a" => (Route.clip R N (i+1) n)
local notation "O" => R.metals.O
local notation "κ" => R.alloy.B.kin
local notation "lo" => (π (i+1))
local notation "bill" => Route.wilson R N p₀ (π (i+1)) M p

set_option maxHeartbeats 800000
lemma issued_writes : PressWrites M 𝒮 C O g a lo T := by
  have ok := lesson_action R pay Q J π Γ hi L (n:=n) cut
  rw [ok, lesson_clip R cut, L.ticket]
  exact CP5Bridge.writes pay R.rolls Q R.alloy ((σ).S.oneStep i n).exact_size capacity (Oak.era R J pay Q π Γ hi capacity L) L.entry clock M v
    (lesson_admitted R pay Q J π Γ hi L conc cut)

-- Keep `t∈Actors`. Canonical `Mentor.student` expects that whole space; can be true smooth tests or stencils.
omit cut L conc -- restore
variable {W : V → Type} (allowed : ∀ i, Set (W i))
variable (rows : ι → Earn.Row A I G (Affinity.Wallet allowed))
  (voter : Cruise.Voter rows
    (Poetry.Agenda.seed pay φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) p capacity.count capacity.stage k (R.alloy.B.a.clock.J i))
  (forecast : Mentor.Forecast pay R.rolls Q φ clock)
local notation "out" => Oak.student (n:=n) R J pay Q π Γ clock hi capacity L forecast allowed rows p voter
local notation "prints" => Cruise.publish pay R.rolls Q R.alloy φ clock capacity
    (Oak.era R J pay Q π Γ hi capacity L) ((σ).S.oneStep i n).exact_size rows p voter L.entry
include cut conc L

lemma student_renders {w : V → ℝ} {grades : V → ℕ} {pieces k' : ℕ} {funds : ℝ}
    (paid : Earn.Scene.Armada out w grades (Poetry.Agenda.seed pay φ (Burn.horizon k) yStage) funds p pieces k') :
    Renderer out (π i) T grades p (Route.wilson R N p₀ lo rows p) ∧
      ∀ (r : ℕ), r ≤ p → ∀ t (z : rule (Coarse G) (R.family.side i n)),
        Summable (clubOutput C O g a lo T rows p r t z) ∧ Summable (globalOutput rows r t) := by
  have prints_ok := issued_writes R pay Q J π Γ hi L conc cut clock capacity rows voter
  have receipt := Cruise.funded pay R.rolls Q R.alloy φ clock capacity (Oak.era R J pay Q π Γ hi capacity L)
    ((σ).S.oneStep i n).exact_size rows p voter L.entry L.studied forecast
  have pos := Poetry.Agenda.stem pay φ (Burn.horizon k) yStage
  have pos' := Poetry.Agenda.belt_p pay (Burn.horizon k) xStage
  refine ⟨press_renders rows _ prints_ok receipt paid pos pos', fun r order t z => ?_⟩
  have costs := printed_discharge (U':=π i) (extra':=T) rows prints prints_ok receipt paid pos pos' r order t z
  exact ⟨costs.1,costs.2.1⟩
end
end YM.Integration.FVA1Physical.MixedResets
