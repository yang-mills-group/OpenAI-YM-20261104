import YM.Integration.WilsonOriginalOccupiedRaffleIndependent
import YM.Integration.WilsonOriginalOrdinaryBochner
import YM.Integration.WilsonOriginalOccupiedFiledSlice
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFreshPrintedGross
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m  ≤  i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)


open Filter MeasureTheory WilsonRootedKioskOccupiedSlip MintClock
local notation "H" => Ψ (i+1)
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "gf" => Coat.gStep (H).beta
local notation "α" => (H).p.supportExponent+1
local notation "lamp" => rendered P.model (H).p (gf)
local notation "D₀" => (∑v:V,grades v)+1
local notation "U₀" => MintClock.Page.temperature G 1 χ
local notation "fee" => WilsonOriginalThreeCompactWallet.fee G (H).p (U₀) (gf) ((σ₀)/4)
  order P.op.count shelf (D₀)
local notation "bill" => (2^(order+shelf+1)/(gf)^(D₀))*
  (Invoice.price (H).p (U₀) (order+shelf+1) P.op.count (α) ((σ₀)/4) G*P.cost)

include cut course in
theorem original (simple:G.Simple) (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    (depth:order ≤ R.alloy.B.a.clock.J (i+1))
    (shelved:shelf ≤ R.alloy.B.a.clock.J i)(slots:P.op.count ≤ Burn.horizon k+2)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1):
    Gross (lamp) P.w (H).p.B (α) (bill) ∧
    |fee|/Willow.haloSlack (H).p.B ≤ 2^(order+shelf+1+(D₀))*χ^((D₀)+2) ∧
    ∀t, Integrable (fun W=>((H).eval W:ℂ) • Poly.pass (bare (lamp) t W)) (prior G _):=by
  have ready:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J (i+1):=hk.trans (R.alloy.B.a.fits.mono (Nat.le_succ_of_le hi))
  have later:=R.alloy.B.a.fits.mono (Nat.le_succ i)
  have actual:=WilsonOriginalOccupiedRaffleIndependent.original R simple warm (f:=i+1) course
    (Nat.le_succ_of_le hi) cut (jet:=Burn.horizon k) ((Nat.le_add_right _ 2).trans ready) depth
    (shelved.trans later) (slots.trans ready) (D₀) halo
  have funding:∀s:(Stock.census V).Mode,(∑v∈s.val,grades v)+1 ≤ (D₀):=fun _=>Nat.succ_le_succ
    (Finset.sum_le_sum_of_subset_of_nonneg (f:=grades) (subset_univ _) (fun _ _ _=>Nat.zero_le _))
  have full:=WilsonMarkedFixedPoleGross.landed P.model P.w grades (H).p P.salary actual.1 (D₀) funding
  letI:Countable P.modelIndex:=P.modelCount
  have env:Envelope (H).eval:=(H).envelope (course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).truep.valid
  have width:0 ≤ (α):=by linarith only [(H).p.exponent_pos]
  exact ⟨full,actual.2,WilsonOriginalOrdinaryBochner.unmasked (H) env (lamp) P.salary.positive width full⟩

end YM.Integration.WilsonOriginalFreshPrintedGross
end
