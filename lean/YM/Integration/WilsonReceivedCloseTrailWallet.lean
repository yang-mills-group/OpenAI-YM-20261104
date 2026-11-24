import YM.Integration.WilsonReceivedCloseHistory
import YM.Integration.WilsonReceivedCloseEndpoint

/-! The terminal birth-scale fee and all subsequent changes of weight on one filed physical trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseTrailWallet
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


local notation "B" => budgetR R
local notation "stage" j:max => (B j)^2*(B (j+1))^7
local notation "carrier" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "trace" p:max i:max f:max y:max l:max => WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books
  ahead actors pieces grades order shelf seats mb source p i f y l

private theorem pages (P₀ : carrier b mb source) {i : ℕ} {mi : m ≤ i}
    {y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L : carrier i mi y} (record : trace P₀ i mi y L) : ∀ z ∈ Ico i b, 2 ≤ B z := by
  induction record with
  | start => simp
  | @step j floor y U L earlier filed factor active paid wages previous =>
    intro z hz
    rcases eq_or_lt_of_le (mem_Ico.mp hz).1 with eq|lt
    · subst z
      let Ω := Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead order shelf
      have bound : Ω ≤ B j := L.issued.Beamwork
      have four : 4 ≤ Ω := MintClock.Page.roofers ..
      linarith only [four,bound]
    · exact previous z (mem_Ico.mpr ⟨lt,(mem_Ico.mp hz).2⟩)

/-- The largest of the two original boundary charges is stage(b)². Its product with the radius
ratio for the actual post is subpower even after every marked leg is restored together. -/
theorem original (P₀ : carrier b mb source) (simple : G.Simple) {i : ℕ} {mi : m ≤ i}
    {y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L : carrier i mi y} (record : trace P₀ i mi y L)
    (degree a : ℕ) {cap η : ℝ} (cn : 0 ≤ cap) (small : 0 < η) (top : b ≤ N)
    (close : PaceR.Close R degree cap m b)
    (ready : (eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple degree
      (2*a) 0 cn small (le_rfl:0≤(0:ℝ)))).choose ≤ b) :
    ∃ d : ℝ, 1 ≤ d ∧ (∀v,L.w v = P₀.w v/d) ∧
      ((stage b)^2*d)^a ≤ (regulatorRun R.family N per b)^(-η) := by
  obtain ⟨ib,d,one,capD,equal⟩ := record.wallet
  have paid := (eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple degree
    (2*a) 0 cn small (le_rfl:0≤(0:ℝ)))).choose_spec b ready m mb close N per top i mi ib 1
      zero_le_one (pages R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ record)
  let t := ∏j ∈ Ico i b, stage j
  have bound : (stage b)^(2*a)*(∏j∈Ico i b,(stage j)^(2*a)) ≤
      (regulatorRun R.family N per b)^(-η) := by simpa using paid
  have t₁ : 1 ≤ t := one.trans capD
  have room : d ≤ t^2 := capD.trans (by simpa only [pow_one] using pow_le_pow_right₀ t₁ (by decide:1≤2))
  refine ⟨d,one,equal,?_⟩
  calc
    _ ≤ ((stage b)^2*t^2)^a := pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (zero_le_one.trans one))
      (mul_le_mul_of_nonneg_left room (sq_nonneg _)) _
    _ = (stage b)^(2*a)*t^(2*a) := by rw [mul_pow,pow_mul,pow_mul]
    _ = (stage b)^(2*a)*(∏j∈Ico i b,(stage j)^(2*a)) := by
      congr 1
      first | exact prod_pow .. | symm; exact prod_pow ..
    _ ≤ _ := bound

end YM.Integration.WilsonReceivedCloseTrailWallet
