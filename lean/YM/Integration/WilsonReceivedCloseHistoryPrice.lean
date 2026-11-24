import YM.Integration.WilsonReceivedCloseHistory

/-! Recovering the physical coefficient on its original marked radii after the funded close descent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseHistoryPrice
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
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))


/-- This date uses the original schedule alone, before the cutoff, volume, source and test. -/
def opening (simple : G.Simple) (degree a q : ℕ) {cap η ε : ℝ} (cn : 0≤cap) (loss : 0<η) (en : 0≤ε) : ℕ :=
  max (eventually_atTop.mp (WilsonReceivedCloseChainFunding.original R simple degree a q cn loss en)).choose
    (max (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose
      (eventually_atTop.mp (WilsonReceivedCloseReentry.small R simple degree cap)).choose)

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max mi:max ib:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i mi (read i ib)
local notation "B" => budgetR R
local notation "g" => regulatorRun R.family N per
local notation "stage" j:max => (B j)^2*(B (j+1))^7

include mb in
theorem at_capture (P₀ : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats b mb source)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (top : b < N)
    (pass : Pass D Q R.alloy R.kit) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J m)
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (simple : G.Simple) (q : ℕ) (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2)
    {ε : ℝ} (ep : 0 < ε) (unit : ε ≤ 1)
    (late : WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ m+1)
    (test : Wallet actors) (degree a : ℕ) {cap η : ℝ} (cn : 0≤cap) (loss : 0<η)
    (ready : opening R simple degree a q cn loss ep.le ≤ b) (close : PaceR.Close R degree cap m b) :
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ Pᵢ : P i mi ib,
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source P₀ i mi (read i ib) Pᵢ ∧ ∀ s : (Stock.census V).Mode, s.val.card ≤ a →
        Pᵢ.rent/Poly.toll Pᵢ.w s ≤
        (g b)^(-η)*(P₀.rent+ε*(3*g b)^q)/Poly.toll P₀.w s := by
  intro i ib mi
  obtain ⟨cash,other⟩ := max_le_iff.mp ready
  obtain ⟨temp,small⟩ := max_le_iff.mp other
  have sizes := (eventually_atTop.mp (WilsonReceivedCloseReentry.small R simple degree cap)).choose_spec b small m mb close N per
  have bands := (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose_spec b temp m mb close N per top.le
  have fund := (eventually_atTop.mp (WilsonReceivedCloseChainFunding.original R simple degree a q cn loss ep.le)).choose_spec
    b cash m mb close N per top.le i mi ib
  obtain ⟨Pᵢ,d,one,more,wallet,bill,issued,trace⟩ := WilsonReceivedCloseHistory.descent R hk D Q π Γ Ψ books ahead
    actors pieces grades order shelf seats mb source P₀ course path top pass scroll chamber month hospital fits narrow
    load packed simple q deep aged ep unit late test (fun j mj jN => ⟨(bands j mj jN).1,sizes j mj jN⟩) i ib mi
  refine ⟨Pᵢ,trace,?_⟩
  intro s arity
  have present (j : ℕ) : 0 ≤ stage j := mul_nonneg (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
    (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
  have funded := fund (fun j => stage j) (fun _ => s.val.card) P₀.rent P₀.active.le
    (fun j hj => ⟨issued j hj,present j,le_rfl,arity⟩)
  have nd := (zero_lt_one.trans_le one).le
  have income : 0≤P₀.rent+∑j∈Ico i b, ε*(g (min N (j+2)))^q := Pᵢ.active.le.trans bill
  have multiplicity : (∏j∈Ico i b,stage j)^s.val.card = ∏j∈Ico i b,(stage j)^s.val.card := by
    first | exact Finset.prod_pow .. | symm; exact Finset.prod_pow ..
  have paid := (mul_le_mul (pow_le_pow_left₀ nd more s.val.card) bill Pᵢ.active.le
    (pow_nonneg (prod_nonneg (fun j _=>present j)) _)).trans
    (by simpa only [←multiplicity] using funded)
  have toll : Poly.toll Pᵢ.w s=Poly.toll P₀.w s/d^s.val.card := by
    unfold Poly.toll
    simp only [wallet,Finset.prod_div_distrib,Finset.prod_const]
  have entered := (Poly.worth P₀.salary.positive s).le
  rw [toll,div_div_eq_mul_div]
  simpa only [mul_comm Pᵢ.rent] using div_le_div_of_nonneg_right paid entered

end YM.Integration.WilsonReceivedCloseHistoryPrice
