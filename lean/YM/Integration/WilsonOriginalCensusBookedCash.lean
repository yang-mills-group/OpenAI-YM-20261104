import YM.Integration.WilsonOriginalCensusPhysicalLoad
import YM.Integration.WilsonOriginalCensusAngularFace
import YM.Integration.WilsonOriginalRestampedCensusFiling
import YM.Integration.WilsonOriginalCensusRestamp
import YM.Integration.WilsonOriginalDepositedCensusBook
import YM.Integration.WilsonOriginalAdjacentCensusFiling
import YM.Integration.WilsonOriginalCensusMount
import YM.Integration.WilsonOriginalFreshJoinedRows
import YM.Integration.WilsonOriginalFreshPrintedGross

/-! Mount the three genuine programs from two adjacent original Wilson posts on a
single optical slice. The signed words read the unmasked output of the upper post
and the incoming independently submitted program of the next lower post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusBookedCash
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀i,RG.Rep G (R.family.side i per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ) (lo:m   ≤   j) (cut:j+1 < N)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type} [Fintype V] [DecidableEq V] {X Y:V→Type}
  [∀v,AddCommGroup (X v)] [∀v,Module ℝ (X v)] [∀v,AddCommGroup (Y v)] [∀v,Module ℝ (Y v)]
  (A:∀v,Set (X v)) (K:∀v,Submodule ℝ (X v)) (A':∀v,Set (Y v)) (K':∀v,Submodule ℝ (Y v))
  (grades grades':V→ℕ)(order shelf seats order' shelf' seats':ℕ)
  (upperLaw:Wallet A → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))
  (lowerLaw:Wallet A' → Config G (R.family.side (j+1) per) → Poly (Stock.census V))
  (high:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A K grades order shelf
    seats (j+1) (Nat.le_succ_of_le lo) upperLaw)
  (low:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A' K' grades' order' shelf' seats' j lo lowerLaw)
local notation "vac" => Ψ (j+1)
local notation "marks" => Stock.census V
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books (Nat.le_succ_of_le lo)
  high.op high.lesson ahead A high.model order high.voter
local notation "Lu" => rendered (student) (vac).p (Coat.gStep (Ψ ((j+1)+1)).beta)
local notation "next" => rendered low.model (vac).p (Coat.gStep (vac).beta)
local notation "home" => (high.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
variable {tariff tariff':(Stock.census V).Mode→ℝ}
  (highBook:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books (Nat.le_succ_of_le lo) ahead
    A K grades order shelf seats upperLaw high tariff)
  (lowBook:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books lo ahead
    A' K' grades' order' shelf' seats' lowerLaw low tariff')


local notation "ζ" => Oak.grade0 R hk D Q π Γ (Nat.le_succ_of_le lo) high.lesson
local notation "gf" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "gc" => Coat.gStep (vac).beta
local notation "stamped" => Mutation.stamp (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) order
local notation "carried" => Mutation.grow (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) order
  (gf) (gc) (vac) high.output
local notation "L" => rendered (stamped) (vac).p (gc)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books (Nat.le_succ_of_le lo) high.op high.lesson ahead order shelf
local notation "w₂" => Stoop.radius high.w ((Ω)^6)

open WilsonOriginalCensusAngularFace
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "fig" => Oak.figureReal R hk D Q π Γ books (Nat.le_succ_of_le lo) high.op high.lesson ahead order shelf
local notation "both" => roster (stamped) low.model
local notation "wages" => sides (w₂) low.w
local notation "costs" => sides (budgetR R (j+1)) low.cost
local notation "degrees" => sides grades grades'
local notation "orders" => sides order order'
local notation "loads" => sides high.op.count low.op.count
local notation "shelves" => sides shelf shelf'

open WilsonEmittedJoinedFares

private theorem inverse {a t d:ℝ}(ha:0<a)(u:ℕ)(base:1   ≤   d)(spent:d^u   ≤   t*a):a⁻¹   ≤   t:=by
  have one:1   ≤   t*a:=(one_le_pow₀ base (n:=u)).trans spent
  simpa only [one_div] using (div_le_iff₀ ha).mpr one

include highBook lowBook in
theorem original (x:Wallet A)(z:Wallet A')(s:(marks).Mode) (coef:Bool→ℝ):
    cash s (wages) coef (costs)   ≤   |coef false| *((Ω)^6)^s.val.card*tariff s*(budgetR R (j+1))+
      |coef true| *tariff' s*low.cost:=by
  have first: (Poly.toll high.w s)⁻¹  ≤  tariff s:=by
    apply inverse (Poly.worth high.salary.positive _) s.val.card
      (d:=WilsonOriginalOccupiedSalary.debit (highBook.row x).regular (highBook.row x).hard) (le_max_left ..)
    rw [←highBook.radius x]
    exact highBook.wage x s
  have second: (Poly.toll low.w s)⁻¹  ≤  tariff' s:=by
    apply inverse (Poly.worth low.salary.positive _) s.val.card
      (d:=WilsonOriginalOccupiedSalary.debit (lowBook.row z).regular (lowBook.row z).hard) (le_max_left ..)
    rw [←lowBook.radius z]
    exact lowBook.wage z s
  have reshape:(Poly.toll (w₂) s)⁻¹=((Ω)^6)^s.val.card*(Poly.toll high.w s)⁻¹:=by
    simp only [Stoop.radius,Poly.toll,div_eq_inv_mul,Finset.prod_mul_distrib,Finset.prod_const,mul_inv,
      inv_pow,inv_inv]
  have budget:0  ≤  budgetR R (j+1):=zero_le_one.trans (budget_pos R)
  have wages₁:=mul_le_mul_of_nonneg_left first (by positivity:0   ≤   ((Ω)^6)^s.val.card)
  rw [←reshape] at wages₁
  have left:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right wages₁ budget) (abs_nonneg (coef false))
  have right:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right second
    (budget_nonneg (low.salary.suggests 0))) (abs_nonneg (coef true))
  unfold WilsonEmittedJoinedFares.cash
  rw [Fintype.sum_bool]
  change |coef true| *((Poly.toll low.w s)⁻¹*low.cost)+
    |coef false| *((Poly.toll (w₂) s)⁻¹*budgetR R (j+1))   ≤   _
  calc _   ≤   |coef true| *(tariff' s*low.cost)+
           |coef false| *((((Ω)^6)^s.val.card*tariff s)*budgetR R (j+1)):=add_le_add right left
       _ = _:=by ring

end YM.Integration.WilsonOriginalCensusBookedCash
end
