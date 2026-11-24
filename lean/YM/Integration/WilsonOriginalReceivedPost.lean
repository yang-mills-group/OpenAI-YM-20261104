import YM.Integration.WilsonOriginalReceivedMeasuredCarry

/-! A paid date of the actual marked Wilson history on one fixed roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
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

/-- The densities in a post are the complete polynomials, before testing an occupied face.
The regular and hard receipts are stored separately so only one hard divisor is spent. -/
structure Post where
  op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i)
  capacity : op.count = seats
  lesson : Lesson (N:=N) R hk D Q π Γ floor
  passport : Earn.Passport (R.family.side (i+1) per) V
  modelIndex : Type
  inputIndex : Type
  outputIndex : Type
  modelCount : Countable modelIndex
  outputCount : Countable outputIndex
  model : modelIndex → Row passport (Stock.census V) G (Wallet actors)
  input : Tint.Incoming passport (Ψ (i+1)) (Wallet actors) inputIndex (Stock.census V)
  output : Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio) (Ψ i)
    (Wallet actors) outputIndex (Stock.census V)
  w : V → ℝ
  cost : ℝ
  rent : ℝ
  affordable : cost ≤ (Oak.expenseReal R hk D Q π Γ books floor op lesson ahead order shelf)⁻¹
  active : 0 < rent
  small : rent ≤ 1
  voter : Cruise.Voter model (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i)
  salary : Scene.Armada model w grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    cost order op.count shelf
  tests : Tableau pieces actors model
  oldTests : Taut passport.support actors pieces input.old
  hardTests : Crown passport.support actors pieces input.hard
  regular : input.old.Paid w (Ψ (i+1)).p.B ((Ψ (i+1)).p.supportExponent+1+1) rent
  forced : input.hard.Paid w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent (LocalComparison.forcedDivisor R.family (i+1))
  represented x : (Tint.Patrol.picture model input).density x = physical x
  issued : Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books floor op lesson ahead actors pieces model input
    w grades order shelf voter rent cost output

/-- The reported post is the normalized physical push of its own represented source. -/
theorem report (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
    (x : Wallet actors) :
    LocalComparison.actualPush R.family N per i (physical x) =
      (Tint.Patrol.report (Oak.student (n:=per) R hk D Q π Γ books floor P.op P.lesson ahead actors P.model
        order P.voter) P.output (Coat.gStep (Ψ (i+1)).beta)).density x :=
  (congrArg (LocalComparison.actualPush R.family N per i) (P.represented x).symm).trans (P.issued.reads x)

end YM.Integration.WilsonOriginalReceivedChain
