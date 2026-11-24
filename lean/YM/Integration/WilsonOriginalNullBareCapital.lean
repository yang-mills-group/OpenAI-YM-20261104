import YM.Integration.WilsonOriginalNullBareInvoice
import YM.Integration.WilsonOlderFreshGraphInvoiceCurrency
import YM.Integration.WilsonOriginalReceivedPost

/-! The column's numerical coupling remains on its physical cutoff. A paid auxiliary post supplies a date-only invoice. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareCapital
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open Pert.Asymptotics
open private monotone from YM.Integration.WilsonMeasuredImpulseCalendar
open scoped Classical BigOperators Topology
variable {G:Gauge}

def Priced {n:Side} (W:Rep G n) (σ:ℝ) (ord shelf seats:ℕ) (allocation:ℝ):Prop:=
  ∃ fac θ:ℝ,Invoice.Supports W.p fac (W.p.supportExponent+2) (Coat.gStep W.beta) σ θ ∧
    Invoice.price W.p fac (ord+shelf+1) seats (W.p.supportExponent+2) θ G ≤ (2:ℝ)^(ord+shelf+1)*allocation
variable (R:Run G) {m n per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:(j:ℕ) → RG.Rep G (R.family.side j per))
  {M:ℕ} (c:Concourse R.alloy R.kit R.T π Γ m M per k Ψ) {φ:ℕ → ℕ}
  (books:Mentor.Offices.Books D R.rolls Q φ) (lo:m ≤ n)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type} [DecidableEq V] [Fintype V] {X:V → Type} [∀ j,AddCommGroup (X j)] [∀ j,Module ℝ (X j)]
  (actors:∀j,Set (X j)) (pieces:∀j,Submodule ℝ (X j)) (grades:V → ℕ)
  (ord shelf seats:ℕ) (source:Wallet actors → Config G (R.family.side (n+1) per) → Poly (Stock.census V))
  (H:WilsonOriginalReceivedChain.Post (N:=M) R hk D Q π Γ Ψ books ahead actors pieces grades
    ord shelf seats n lo source)
local notation "figure" => Oak.figureReal R hk D Q π Γ books lo H.op H.lesson ahead ord shelf
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J n)
local notation "Hβ" => R.alloy.B.a.clock.hatBeta n


include c H in
theorem appointed (simple:G.Simple) (live:n<M) (large:2 ≤ Hβ)
    (W:Rep G (R.family.side n per)) (point:W.p=R.family.path.levels.budget n)
    (beta:W.beta=(R.family.path.rep n per n).beta):
    Priced W σ ord shelf seats (budgetR R n):=by
  obtain ⟨fee,rate⟩:=WilsonOriginalNullBareInvoice.appointed R hk D Q π Γ Ψ c books lo ahead actors pieces grades
    ord shelf seats source H simple live large W point beta
  exact ⟨_,_,fee,rate⟩
end YM.Integration.WilsonOriginalNullBareCapital
