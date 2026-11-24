import YM.Integration.WilsonOriginalReceivedFiledChain

/-! Restriction of a certified physical history to a later reporting date,
with the appointed lesson, both marked intakes and the actual post unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredDateRestriction
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open WilsonOriginalReceivedChain
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats i : ℕ) (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))


variable {b:ℕ} (left:m ≤ b)
local notation "act" => hk.trans (R.alloy.B.a.fits.mono left)

def post (P:Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
    (right:b ≤ i) :
    Post (N:=N) R act D Q π Γ Ψ books ahead actors pieces grades order shelf seats i right physical where
  op := P.op
  capacity := P.capacity
  lesson := ⟨P.lesson.entry,P.lesson.studied,P.lesson.ticket,P.lesson.stake,P.lesson.eats⟩
  passport := P.passport
  modelIndex := P.modelIndex
  inputIndex := P.inputIndex
  outputIndex := P.outputIndex
  modelCount := P.modelCount
  outputCount := P.outputCount
  model := P.model
  input := P.input
  output := P.output
  w := P.w
  cost := P.cost
  rent := P.rent
  affordable := P.affordable
  active := P.active
  small := P.small
  voter := P.voter
  salary := P.salary
  tests := P.tests
  oldTests := P.oldTests
  hardTests := P.hardTests
  regular := P.regular
  forced := P.forced
  represented := P.represented
  issued := ⟨P.issued.earning, P.issued.school, P.issued.repair, P.issued.force, P.issued.local_, P.issued.kept, P.issued.tuition, P.issued.paidForce, P.issued.reads, P.issued.Waffle, P.issued.Beamwork, P.issued.effort⟩

include left in
theorem course (run:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) :
    Concourse R.alloy R.kit R.T π Γ b N per k Ψ :=
  ⟨⟨run.1.start, fun i hi hn=>run.1.walk i (left.trans hi) hn,
    fun i hi hn=>run.1.visit i (left.trans hi) hn,fun i hi hn=>run.1.pace i (left.trans hi) hn⟩,
    fun i hi hn=>run.2 i (left.trans hi) hn⟩

include left in
theorem path (road:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) :
    PlanV.Path D R.alloy Q (Burn.horizon k) N b π Γ :=
  ⟨fun i hi hn=>road.1 i (left.trans hi) hn,road.2.1,fun i hi hn=>road.2.2 i (left.trans hi) hn⟩

end YM.Integration.WilsonMeasuredDateRestriction
