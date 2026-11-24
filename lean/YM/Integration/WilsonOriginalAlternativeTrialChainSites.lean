import YM.Integration.WilsonOriginalAlternativeTrialChainClock
import YM.Integration.WilsonOriginalAlternativeTrialHomes
import YM.Integration.WilsonReceivedFirstTraceHistory
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialChainSites
open WilsonReceivedFirstTrace WilsonThermometerMixedCollarSubpower
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)

variable (W : Registration (m:=m) (N:=N) (k:=k) R D Q π Γ Ψ books ahead actors shelf seats)
local notation "carrier" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y



variable (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))
  (P₀ : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats b mb source)
  (c₀ : Countable P₀.inputIndex) (top : b<N) (q : ℕ) (ε : ℝ)

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "g" => regulatorRun R.family N per
local notation "store" U:max count:max cut:max => install R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W U count cut

theorem original {i:ℕ}{floor:m ≤ i}{cut:i<N}
    {y:Wallet actors → Config G (R.family.side (i+1) per)→Poly (Stock.census V)}
    {L:carrier i floor y}{cl:Countable L.inputIndex}
    (all:Chain R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W mb source P₀ c₀ top q ε i floor cut y L cl):
    ∀(age:i ≤ b)(o:V→Site (R.family.side i per)),
      (∀v,P₀.passport.origin v=(R.family.S.toDepth (age.trans (Nat.le_succ b)) per).embed (o v)) →
      ∀v,(L.passport.coarser (R.family.path.levels.clock.op i per).ratio).origin v=o v:=by
  intro age o starts
  have tr:=Chain.trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W mb source P₀ c₀ top q ε all
  exact WilsonOriginalAlternativeTrialHomes.received R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mb source (store P₀ c₀ top) tr (Nat.succ_le_of_lt top) age o starts

end YM.Integration.WilsonOriginalAlternativeTrialChainSites
end
