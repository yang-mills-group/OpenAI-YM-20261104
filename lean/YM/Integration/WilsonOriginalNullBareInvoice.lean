import YM.Integration.WilsonOlderFreshGraphInvoiceCurrency
import YM.Integration.WilsonOriginalReceivedPost

/-! The column's numerical coupling remains on its physical cutoff. A paid auxiliary post supplies a date-only invoice. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareInvoice
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
theorem crossed {C : Family G} (H : C.Makes) (hg : G.Simple) (N M p k j : ℕ) (kj : k≤j) (kn : k≤N) (jn : j≤M) :
    regulatorRun C M p j ≤ 2*regulatorRun C N p k := by
  have k0 := (H.wilson.represents N p k kn).band
  have j0 := (H.wilson.represents M p j jn).band
  have mono := monotone hg C.path.levels kj
  have ha : 0 < C.path.β M p j := (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed j))).trans_le j0.1
  have hb : 0 < C.path.β N p k := (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed k))).trans_le k0.1
  have h : C.path.β N p k ≤ 4*C.path.β M p j := by linarith only [k0.2,j0.1,mono]
  have sq := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 from by norm_num] at sq
  unfold regulatorRun; have jpos := Real.sqrt_pos.2 ha; have kpos := Real.sqrt_pos.2 hb
  rw [←one_div,← div_eq_mul_inv,(div_le_div_iff₀ jpos kpos)]; simpa using sq

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

include c in
theorem appointed (simple:G.Simple) (live:n<M) (large:2 ≤ Hβ)
    (W:Rep G (R.family.side n per)) (point:W.p=R.family.path.levels.budget n)
    (beta:W.beta=(R.family.path.rep n per n).beta) :
    Invoice.Supports W.p (2*(figure).mist) (W.p.supportExponent+2) (Coat.gStep W.beta) σ (figure).limitC ∧
    Invoice.price W.p (2*(figure).mist) (ord+shelf+1) seats (W.p.supportExponent+2) (figure).limitC G
      ≤ (2:ℝ)^(ord+shelf+1)*budgetR R n :=by
  have he:W.p=(Ψ n).p:=point.trans (c.1.walk n lo live.le).truep.point.symm
  have up:Coat.gStep (Ψ (n+1)).beta=regulatorRun R.family M per (n+1):=by
    rw [(c.1.walk (n+1) (Nat.le_succ_of_le lo) live).beta];rfl
  have low:Coat.gStep W.beta=regulatorRun R.family n per n:=by rw [beta];rfl
  have step:Coat.gStep (Ψ (n+1)).beta ≤ 2*Coat.gStep W.beta:=by
    rw [up,low]
    exact crossed R.makes simple n M per n (n+1) (Nat.le_succ _) le_rfl live
  have band:= (R.makes.wilson.represents n per n le_rfl).band
  have enough:1 ≤ (R.family.path.rep n per n).beta:=by
    have lowBand:R.alloy.B.a.clock.hatBeta n/2 ≤ (R.family.path.rep n per n).beta:=band.1
    linarith only [lowBand,large]
  have pos:0<Coat.gStep W.beta:=by rw [beta];exact inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le enough))
  have limit:Coat.gStep W.beta ≤ 1:=by
    rw [beta];exact inv_le_one_of_one_le₀ (by rw [←Real.sqrt_one];exact Real.sqrt_le_sqrt enough)
  have scopes:=H.issued.Waffle.soon
  have quote:=H.issued.Waffle.quote
  have compat:(figure).afterwards=σ:=by rfl
  rw [compat] at scopes
  have sold:Invoice.price (Ψ n).p (figure).mist (ord+shelf+1) seats ((Ψ n).p.supportExponent+2) (figure).limitC G ≤ budgetR R n:=by
    have price:Invoice.price (Ψ n).p (figure).mist (figure).cap (figure).count ((Ψ n).p.supportExponent+1+1)
        (figure).limitC G ≤ budgetR R n:=quote.trans H.issued.Beamwork
    have rank:(figure).cap=ord+shelf+1:=by rfl
    have count:(figure).count=seats:=H.capacity
    simpa only [rank,count,add_assoc,one_add_one_eq_two] using price
  rw [he]
  constructor
  · exact WilsonOlderFreshGraphInvoiceCurrency.shift (by simpa only [add_assoc,one_add_one_eq_two] using scopes) step pos limit
  · rw [WilsonOlderFreshGraphInvoiceCurrency.quote]
    exact mul_le_mul_of_nonneg_left sold (by positivity)
end YM.Integration.WilsonOriginalNullBareInvoice
