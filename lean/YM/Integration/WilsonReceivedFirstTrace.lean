import YM.Integration.WilsonOriginalReceivedFirstEnrollment
import YM.Integration.WilsonOriginalReceivedCountedChain
import YM.Integration.WilsonReceivedCloseHistory

/-! A genuine repeated first-join registration retains the same incoming finite model,
all original hard and smooth inputs, every child passport, and the purchased radii. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedFirstTrace
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)

/-- The original elected receipts used to expose the two physical mergers at each date. -/
structure Registration where
  simple : G.Simple
  course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ
  scroll : VowsR.LawScroll G φ
  chamber : VowsR.Chamber scroll R.kit D Q books
  hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay
  load : seats ≤ Burn.horizon k+2
  narrow : shelf ≤ R.alloy.B.a.clock.J m
  test : Wallet actors

variable (W : Registration (m:=m) (N:=N) (k:=k) R D Q π Γ Ψ books ahead actors shelf seats)
local notation "carrier" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y

/-- Store the actually selected first-join output. All input data stay on their old addresses. -/
noncomputable def install {i : ℕ} {floor : m ≤ i}
    {y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    (U : carrier i floor y) (count : Countable U.inputIndex) (cut : i<N) : carrier i floor y := by
  letI : Countable U.inputIndex := count
  exact WilsonOriginalReceivedFirstEnrollment.installed R hk D Q π Γ Ψ books ahead actors
    pieces grades order shelf seats i floor y U W.simple cut W.course W.scroll W.chamber W.hospital
    (U.capacity.le.trans W.load) (W.narrow.trans (R.alloy.B.a.fits.mono floor)) W.test

local notation "store" U:max c:max cut:max => install R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W U c cut

theorem filed {j : ℕ} {floor : m ≤ j}
    {y : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V)}
    {U : carrier (j+1) (floor.trans (Nat.le_succ j)) y}
    {L : carrier j floor (fun x => LocalComparison.actualPush R.family N per (j+1) (y x))}
    (entry : Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor y U L)
    (count : Countable L.inputIndex) (cut : j<N) :
    Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor y U (store L count cut) :=
  ⟨entry.passport, entry.names, entry.model, entry.income, entry.hard⟩

end YM.Integration.WilsonReceivedFirstTrace
