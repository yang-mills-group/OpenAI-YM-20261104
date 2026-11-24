import YM.Integration.WilsonOriginalThermometerFiledPositions
import YM.Integration.WilsonOriginalOccupiedClock

noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialClock
open WilsonReceivedCloseHistory
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D : Roots (G := G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ  →  Layout G) (Γ : ℕ  →  Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ  →  ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V  →  Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V  →  ℕ)
  (order shelf seats : ℕ) (mb : m   ≤   b)
  (source : Wallet actors  →  Config G (R.family.side (b+1) per)  →  Poly (Stock.census V))

local notation "carrier" i : max f:max y : max => Post (N := N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y



open WilsonThermometerMixedCollarSubpower
open private YM.Integration.WilsonOriginalOccupiedClock.one from YM.Integration.WilsonOriginalOccupiedClock
local notation "heat" i:max => R.family.path.levels.clock.hatBeta i
local notation "B" => budgetR R
private theorem ceiling (simple:G.Simple) {j:ℕ} (bound:j ≤ b):
    B j ≤ Real.exp ((scale (heat (b+1)))^3):=by
  exact (le_max_right 1 (B j)).trans (YM.Integration.WilsonOriginalOccupiedClock.one R simple (Nat.succ_le_succ bound))

theorem original (P₀:carrier b mb source) {i:ℕ} {floor:m  ≤  i}
    {y:Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L:carrier i floor y}
    (tr:Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ i floor y L)
    (simple:G.Simple):
    let Ω:=Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead order shelf
    let z:=scale (heat (b+1))
    ∀v:V,((Stoop.radius L.w (Ω^6)) v)⁻¹  ≤ 
      (P₀.w v)⁻¹*Real.exp ((9*((b-i:ℕ):ℝ)+6)*z^3):=by
  intro Ω z v
  obtain ⟨ib,h,one,rise,equal⟩:=tr.wallet
  let t:=Real.exp (z^3)
  have tp:0<t:=Real.exp_pos _
  have bound (j:ℕ) (jb:j ≤ b): B j  ≤ t:=ceiling R simple jb
  have stage (j:ℕ) (jb:j∈Ico i b):(B j)^2*(B (j+1))^7  ≤ t^9:=by
    have inside:=mem_Ico.mp jb
    calc _  ≤  t^2*t^7:=mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans (budget_pos R)) (bound j inside.2.le) _)
                             (pow_le_pow_left₀ (zero_le_one.trans (budget_pos R)) (bound (j+1) inside.2) _)
                             (pow_nonneg (zero_le_one.trans (budget_pos R)) _) (sq_nonneg _)
         _=t^9:=by ring
  have mult:h  ≤  t^(9*(b-i)):=by
    apply rise.trans
    calc _  ≤  ∏_j∈Ico i b,t^9:=Finset.prod_le_prod
            (fun j _=>mul_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans (budget_pos R)) _)) stage
         _= _:=by rw [Finset.prod_const,Nat.card_Ico,pow_mul]
  have rate:Ω ≤ t:=L.issued.Beamwork.trans (bound i ib)
  have paid:Ω^6*h  ≤  t^(9*(b-i)+6):=by
    rw [pow_add,mul_comm]
    exact mul_le_mul mult (pow_le_pow_left₀ (zero_le_one.trans L.issued.Waffle.cool) rate 6)
      (pow_nonneg (zero_le_one.trans L.issued.Waffle.cool) 6) (pow_nonneg tp.le _)
  have math:t^(9*(b-i)+6)=Real.exp ((9*((b-i:ℕ):ℝ)+6)*z^3):=by
    dsimp only [t]
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← math,Stoop.radius,equal,inv_div,div_div_eq_mul_div]
  calc _ =(P₀.w v)⁻¹*(Ω^6*h):=by ring
       _  ≤  _ :=mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr (P₀.salary.positive v).le)
end YM.Integration.WilsonOriginalAlternativeTrialClock
end
