import YM.Integration.WilsonOriginalOccupiedFiledSlice
import YM.Integration.WilsonMeasuredSemesterSubpower

/-! The actual returned original gallery can be reduced to its unit budget at polynomial price. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedFiledFare
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

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter

local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "lamps" => rendered student (Ψ i).p oldG
local notation "gauge" => Tint.Patrol.report student P.output oldG
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "cash" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G*
  ((fig).produce (sheet).ratio.count*P.cost)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "marks" => Stock.census V

local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "ready" l:max => WilsonMeasuredSemesterSubpower.onset R l (by norm_num:0<(1:ℝ))
include course cut in
theorem original (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow:shelf ≤ R.alloy.B.a.clock.J i)(load:P.op.count ≤ Burn.horizon k+2)
    (one:ready 1 ≤ i)(more:ready P.op.count ≤ i)(rented:P.rent ≤ 1)
    (p:ℕ)(ε:ℝ)(small:ε*g^p ≤ 1):
    WilsonOriginalOccupiedSalary.debit (cash+((8*Ω^P.op.count)*P.rent+ε*g^p)) 1 ≤ 10*χ:=by
  have e:=P.issued.Waffle
  have c0:0 ≤ P.cost:=budget_nonneg (P.salary.suggests 0)
  have enough:(fig).produce (sheet).ratio.count*P.cost ≤ 1:=calc
    _ ≤ Ω*P.cost:=mul_le_mul_of_nonneg_right e.earns c0
    _ ≤ Ω*Ω⁻¹:=mul_le_mul_of_nonneg_left P.affordable e.paysAbove.le
    _=1:=mul_inv_cancel₀ e.paysAbove.ne'
  have earned:cash ≤ Ω:=(mul_le_of_le_one_right e.minted.le enough).trans e.quote
  have first:=WilsonMeasuredSemesterSubpower.charged R hk D Q π Γ Ψ course books hi cut ahead actors pieces
    grades order shelf seats physical P 1 (by norm_num:0<(1:ℝ)) one pass hospital narrow load
  have power:=WilsonMeasuredSemesterSubpower.charged R hk D Q π Γ Ψ course books hi cut ahead actors pieces
    grades order shelf seats physical P P.op.count (by norm_num:0<(1:ℝ)) more pass hospital narrow load
  simp only [Real.rpow_one,pow_one] at first
  simp only [Real.rpow_one] at power
  have χ₁:1 ≤ χ:=(R.alloy.B.a.fits.delayed _).le
  have amount:(8*Ω^P.op.count)*P.rent ≤ 8*Ω^P.op.count:=mul_le_of_le_one_right
    (mul_nonneg (by norm_num) (pow_nonneg e.paysAbove.le _)) rented
  unfold WilsonOriginalOccupiedSalary.debit
  apply max_le
  · linarith only [χ₁]
  apply max_le
  · linarith only [earned,first,power,amount,small,χ₁]
  · linarith only [χ₁]

end YM.Integration.WilsonOriginalOccupiedFiledFare
