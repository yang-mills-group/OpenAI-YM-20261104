import YM.Integration.WilsonReceivedCloseStationedGrade
import YM.Integration.WilsonReceivedCloseOrdinaryRoster

/-! All complete Wilson histories started on the original inverse-calibrated marker aperture. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseStationedFaces
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
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
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per



local notation "bill" u:max a:max p:max => WilsonReceivedCloseStationedGrade.fee u 1 a p
local notation "stage" => (budgetR R b)^2*(budgetR R (b+1))^7

theorem original (P₀ : P b mb source) (top : b<N) (simple : G.Simple)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (kfit : k ≤ R.alloy.B.a.clock.J m)
    (protection : ∀ x k : ℕ, k ≤ x → ∀ β : ℝ, R.alloy.delay.betaEntry x ≤ β →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2) ≤ β)
    (law : VowsR.LawScroll G φ) (chamber : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (a d q prec degree span : ℕ) {cap u H angleCap ε:ℝ} (cn : 0≤cap) (u1:1≤u)
    (hc:0≤angleCap) (ep:0<ε)
    (reserve:2*d*a+(q+(2*d+1)*a+1+a)+3≤prec) (orderFits:a+(q+(2*d+1)*a+1)≤order+1)
    (birth:∀v, (P₀.w v)⁻¹≤u*((g b)⁻¹)^(2*d))
    (rent:P₀.rent≤(g b)^prec)
    (close:PaceR.Close R degree cap m b)
    (budget:(eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple degree
      (2*2) 0 cn (η:=1) zero_lt_one (le_rfl:0≤(0:ℝ)))).choose ≤ b)
    (clock:(eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose ≤ b)
    (birthCalendar:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b)
    (cooled:(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ b)
    (selected:(eventually_atTop.mp (WilsonReceivedLogWindow.original R simple D φ protection grades
      order shelf k seats span H angleCap hc)).choose ≤ m)
    (earnDate:(eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
      (WilsonReceivedCloseStationedGrade.nonneg u1 (zero_le_one:0≤(1:ℝ)) a prec) zero_lt_one)).choose ≤ b)
    (valueDate:(eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
      (WilsonReceivedCloseOrdinaryGrade.nonneg (Stock.census V) a (2*d+1) q (zero_le_one.trans u1)) ep)).choose ≤ b)
    (weighted:WilsonReceivedCloseSlate.Paid R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
      source P₀ top a span H angleCap P₀.w (fun _=>(g b)^(-(1:ℝ))*(P₀.rent+2*1*(3*g b)^prec))) :
    WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
        source P₀ univ (u*((g b)⁻¹)^(2*d+1)) ∧
      WilsonReceivedCloseOrdinaryRoster.Served R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
        source P₀ top span H angleCap univ a (u*((g b)⁻¹)^(2*d+1)) ((g b)^(q+(2*d+1)*a+1+a)) (ε*(g b)^q) := by
  let x:=g b
  obtain ⟨xp,small⟩:0<x ∧ 3*x≤1:=(eventually_atTop.mp
    (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec b cooled N per top.le
  have x₁:x≤1:=by linarith only [xp,small]
  have positive:0≤u*(x⁻¹)^(2*d):=mul_nonneg (zero_le_one.trans u1) (pow_nonneg (inv_nonneg.mpr xp.le) _)
  have stage1 : 1 ≤ stage :=one_le_mul_of_one_le_of_one_le (one_le_pow₀ (budget_pos R)) (one_le_pow₀ (budget_pos R))
  have named:=WilsonReceivedCloseNamedWallet.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
    seats mb source P₀ univ simple top d degree cn u1 (fun v _=>by
      have own:=birth v
      rw [←one_div,div_le_iff₀ (P₀.salary.positive v)] at own
      exact own.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left positive (one_le_pow₀ stage1))
        (P₀.salary.positive v).le)) close budget cooled
  let f:=u*(x⁻¹)^(2*d)
  have one:=WilsonReceivedCloseSlate.reprice R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
    source P₀ top a span H angleCap (w':=fun _=>1) (c:=fun _=>f^a)
    (B':=fun _=>bill u a prec*(x^(-(1:ℝ))*x^(-(1:ℝ)))*x^(prec-2*d*a)) weighted (fun s h _=>
      ⟨pow_nonneg positive _,WilsonReceivedCloseStationedGrade.remove xp x₁ u1 h P₀.w P₀.salary.positive
        (fun v _=>birth v),WilsonReceivedCloseStationedGrade.grade xp x₁ u1 zero_le_one rent (by omega)⟩)
  have funds:=WilsonReceivedCloseFaceIncome.original R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats mb source P₀ top simple course kfit protection law chamber fund univ a
    (q+(2*d+1)*a+1+a) prec d span (bill u a prec) u 1 H angleCap
    (WilsonReceivedCloseStationedGrade.nonneg u1 zero_le_one a prec) zero_lt_one hc reserve
    (fun _=>1) (fun _ _=>rfl) named one birthCalendar cooled selected earnDate
  refine ⟨named,?_⟩
  apply WilsonReceivedCloseOrdinaryRoster.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
    seats mb source P₀ top simple univ a (2*d+1) q degree span cap u H angleCap ε u1 ep orderFits _
    close clock birthCalendar cooled valueDate
  simpa only [one_mul] using funds

end YM.Integration.WilsonReceivedCloseStationedFaces
