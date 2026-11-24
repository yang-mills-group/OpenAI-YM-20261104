import YM.Integration.WilsonOriginalAlternativeTrialClock
import YM.Integration.WilsonReceivedFirstTraceHistory
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialChainClock
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
    let Ω:=Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead order shelf
    ∀v:V,((Stoop.radius L.w (Ω^6)) v)⁻¹ ≤ (P₀.w v)⁻¹*
      Real.exp ((9*((b-i:ℕ):ℝ)+6)*(scale (R.family.path.levels.clock.hatBeta (b+1)))^3):=by
  have tr:=Chain.trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W mb source P₀ c₀ top q ε all
  exact WilsonOriginalAlternativeTrialClock.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mb source (store P₀ c₀ top) (L:=store L cl cut) tr W.simple

end YM.Integration.WilsonOriginalAlternativeTrialChainClock
end
