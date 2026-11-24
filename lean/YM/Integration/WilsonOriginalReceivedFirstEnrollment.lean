import YM.Integration.WilsonOriginalReceivedFirstPost
import YM.Integration.WilsonOriginalFirstJoinBuffered
import YM.Integration.WilsonOriginalReceivedPost
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedFirstEnrollment
open WilsonOriginalReceivedChain
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

local notation "PaidDate" => WilsonOriginalReceivedChain.Post (N:=N) (V:=V) (X:=X) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical
variable (P : WilsonOriginalReceivedChain.Post (N:=N) (V:=V) (X:=X) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
local instance : Countable P.modelIndex := P.modelCount
variable (simple : G.Simple) (cut : i<N) (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
  (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (load : P.op.count ≤ Burn.horizon k+2) (wide : shelf ≤ R.alloy.B.a.clock.J i)
  (test : Wallet actors)
local notation "fine" => Ψ (i+1)
local notation "cal" => Classical.choice (Oak.agrees R hk D Q π Γ Ψ course floor cut P.lesson)
local notation "budget" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf

private theorem regular : P.input.old.Paid P.w (fine).p.B (fine).p.supportExponent P.rent :=
  Lamps.tenure _ P.w P.salary.positive P.regular (by linarith)

private theorem hard : P.input.hard.Paid P.w (fine).p.B (fine).p.supportExponent 1 := by
  apply Hard.mono _ P.forced
  exact Real.sqrt_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _)))

private theorem affordable : P.cost ≤ 1 := P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
local notation "reg" => regular R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical P
local notation "forced" => hard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical P
local notation "entry" => affordable R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical P
variable [Countable P.inputIndex]
local notation "onCourse" op:max => op R simple hk D Q π Γ Ψ course scroll books chamber floor cut P.op P.lesson cal
  ahead hospital actors pieces P.model P.input P.w grades order shelf P.voter P.rent P.cost load wide
  P.salary P.tests test P.oldTests P.hardTests reg forced entry P.active P.small


/-- Store the measured output with its genuine first-contact registration. All incoming
coordinates, including the original lesson used in the next radius, are literal projections of P. -/
noncomputable def installed : PaidDate :=
  let result := onCourse Oak.Buffered.first_arrival
  let idx := Classical.choose result
  let supplies := Classical.choose_spec result
  let physicalOut := Classical.choose supplies.2
  let story := (Classical.choose_spec supplies.2).1
  {P with outputIndex:=idx, outputCount:=supplies.1, output:=physicalOut, issued:=story}

local notation "elected" => installed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical
  P simple cut course scroll chamber hospital load wide test
local notation "old" => WilsonOriginalReceivedFirstPost.hardAt R hk D Q π Γ Ψ books ahead actors pieces grades
  order shelf seats i floor physical P simple cut course scroll chamber hospital load wide test

theorem selected : (elected).output.hard = old := by
  let result := onCourse Oak.Buffered.first_arrival
  exact (Classical.choose_spec (Classical.choose_spec result).2).2

end YM.Integration.WilsonOriginalReceivedFirstEnrollment
