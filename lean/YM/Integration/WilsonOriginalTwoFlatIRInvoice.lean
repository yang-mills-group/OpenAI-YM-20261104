import YM.Integration.WilsonOriginalNullBareInvoice
import YM.Integration.WilsonMeasuredSemesterSubpower
import YM.Integration.WilsonMarkedFixedPoleGross

/-! The genuine marked teacher at capture sells its full two-unit support
width to a newly submitted independent word at the measured lower coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRInvoice
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators Topology
variable {G:Gauge}
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

local notation "P" => Ψ n
local notation "g" => Coat.gStep (P).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books lo H.op H.lesson ahead ord shelf
local notation "width" => ((P).p.supportExponent+2)
local notation "upper" => (R.alloy.B.a.clock.hatBeta (n+1))

include c in
theorem original (simple:G.Simple)(live:n<M)(large:2≤Hβ)
    (pass:Pass D Q R.alloy R.kit)(hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved:shelf≤R.alloy.B.a.clock.J n)(load:H.op.count≤Burn.horizon k+2)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ))≤n):
    Invoice.Supports (P).p (2*(figure).mist) (width) (g) (σ) (figure).limitC ∧
      Invoice.price (P).p (2*(figure).mist) (ord+shelf+1) seats (width) (figure).limitC G ≤
        (2:ℝ)^(ord+shelf+1)*upper:=by
  have up:Coat.gStep (Ψ (n+1)).beta=regulatorRun R.family M per (n+1):=by
    rw [(c.1.walk (n+1) (Nat.le_succ_of_le lo) live).beta];rfl
  have low:(g)=regulatorRun R.family M per n:=by rw [(c.1.walk n lo live.le).beta];rfl
  have rate:Coat.gStep (Ψ (n+1)).beta≤2*(g):=by rw [up,low];exact WilsonOriginalNullBareInvoice.crossed R.makes simple M M per n (n+1) (Nat.le_succ _) live.le live
  have enough:1≤(P).beta:=by
    rw [(c.1.walk n lo live.le).beta]
    have x:Hβ/2≤(R.family.path.rep M per n).beta:=(R.makes.wilson.represents M per n live.le).band.1
    change 1≤(R.family.path.rep M per n).beta
    linarith only [x,large]
  have pos:0<(g):=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le enough))
  have lim:(g)≤1:=inv_le_one_of_one_le₀ (by rw [←Real.sqrt_one];exact Real.sqrt_le_sqrt enough)
  have grant:=H.issued.Waffle.soon
  have scale:(figure).afterwards=(σ):=rfl
  rw [scale] at grant
  have cash:=WilsonMeasuredSemesterSubpower.charged R hk D Q π Γ Ψ c books lo live ahead actors pieces grades ord shelf seats
    source H 1 (by norm_num:0<(1:ℝ)) onset pass hospital shelved load
  simp only [pow_one,Real.rpow_one] at cash
  have fare:Invoice.price (P).p (figure).mist (ord+shelf+1) seats (width) (figure).limitC G≤upper:=by
    have z:Invoice.price (P).p (figure).mist (figure).cap (figure).count ((P).p.supportExponent+1+1) (figure).limitC G≤upper:=H.issued.Waffle.quote.trans cash
    have rank:(figure).cap=ord+shelf+1:=rfl
    have count:(figure).count=seats:=H.capacity
    simpa only [rank,count,add_assoc,one_add_one_eq_two] using z
  constructor
  · exact WilsonOlderFreshGraphInvoiceCurrency.shift (by simpa only [add_assoc,one_add_one_eq_two] using grant) rate pos lim
  · rw [WilsonOlderFreshGraphInvoiceCurrency.quote];exact mul_le_mul_of_nonneg_left fare (by positivity)

end YM.Integration.WilsonOriginalTwoFlatIRInvoice
