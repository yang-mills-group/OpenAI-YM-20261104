import YM.Integration.WilsonReceivedCloseTrailWallet
import YM.Integration.WilsonReceivedClosePhysicalBirths

/-! Return all raw marker-width inverses on the same original filed close trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseNamedWallet
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



local notation "stage" => (budgetR R b)^2*(budgetR R (b+1))^7

def Sold (P₀ : P b mb source) (active : Finset V) (price : ℝ) : Prop :=
  ∀ i (ib : i ≤ b) (mi : m ≤ i) (L : P i mi (read i ib)),
    WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ i mi (read i ib) L →
    (∀ v ∈ active, (L.w v)⁻¹ ≤ price) ∧
    ∀ A ∈ active, ∀ B ∈ active, ∀ C ∈ active, (min (L.w A * L.w B) (L.w C))⁻¹ ≤ price^2

theorem original (P₀ : P b mb source) (active : Finset V) (simple : G.Simple) (top : b<N)
    (D₀ degree : ℕ) {cap unit : ℝ} (cn : 0 ≤ cap) (unit₁ : 1 ≤ unit)
    (birth : ∀v ∈ active, 1 ≤ stage^2*(unit*((g b)⁻¹)^(2*D₀))*P₀.w v)
    (close : PaceR.Close R degree cap m b)
    (budget : (eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple degree
      (2*2) 0 cn (η:=1) zero_lt_one (le_rfl:0≤(0:ℝ)))).choose ≤ b)
    (cooled : (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ b) :
    Sold R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ active
      (unit*((g b)⁻¹)^(2*D₀+1)) := by
  intro i ib mi L record
  obtain ⟨d,one,radius,room⟩ := WilsonReceivedCloseTrailWallet.original R hk D Q π Γ Ψ books ahead actors pieces
    grades order shelf seats mb source P₀ simple record degree 2 cn zero_lt_one top.le close budget
  have cold := (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec b cooled N per top.le
  let y := (g b)⁻¹
  let limit := unit*y^(2*D₀+1)
  have y₁ : 1 ≤ y := by
    rw [show y=1/(g b) by simp only [y,one_div],le_div_iff₀ cold.1,one_mul]
    linarith only [cold.1,cold.2]
  have limit₁ : 1 ≤ limit := one_le_mul_of_one_le_of_one_le unit₁ (one_le_pow₀ y₁)
  have edge₁ : 1 ≤ stage := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (budget_pos R)) (one_le_pow₀ (budget_pos R))
  have capD : stage^2*d ≤ y := by
    have raised : 1 ≤ stage^2*d := one_le_mul_of_one_le_of_one_le (one_le_pow₀ edge₁) one
    have up : stage^2*d ≤ (stage^2*d)^2 := by simpa only [pow_one] using pow_le_pow_right₀ raised (by decide:1≤2)
    exact up.trans (by simpa only [y,Real.rpow_neg_one] using room)
  have exactPrice (v : V) (seen : v∈active) : (L.w v)⁻¹ ≤ limit := by
    rw [radius v,inv_div,div_le_iff₀ (P₀.salary.positive v)]
    calc
      d = d*1 := by ring
      _ ≤ d*(stage^2*(unit*y^(2*D₀))*P₀.w v) :=
        mul_le_mul_of_nonneg_left (birth v seen) (zero_le_one.trans one)
      _ = (stage^2*d)*(unit*y^(2*D₀))*P₀.w v := by ring
      _ ≤ y*(unit*y^(2*D₀))*P₀.w v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right capD
          (mul_nonneg (zero_le_one.trans unit₁) (pow_nonneg (zero_le_one.trans y₁) _))) (P₀.salary.positive v).le
      _ = limit*P₀.w v := by simp only [limit,pow_succ];ring
  refine ⟨exactPrice,?_⟩
  intro A inA B inB C inC
  rcases le_total (L.w A*L.w B) (L.w C) with old | counter
  · rw [min_eq_left old,mul_inv, sq]
    exact mul_le_mul (exactPrice A inA) (exactPrice B inB) (inv_nonneg.mpr (L.salary.positive B).le)
      (zero_le_one.trans limit₁)
  · rw [min_eq_right counter]
    exact (exactPrice C inC).trans (by simpa only [pow_one] using pow_le_pow_right₀ limit₁ (by decide:1≤2))

end YM.Integration.WilsonReceivedCloseNamedWallet
