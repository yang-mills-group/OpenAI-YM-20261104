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
namespace YM.Integration.WilsonOriginalCensusAperture
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


def charged (w:V→ℝ)(s:(Stock.census V).Mode):(Stock.census V).Mode:=
  ⟨s.val.filter (fun v=>1 ≤ (w v)⁻¹),Finset.mem_univ _⟩

theorem selected (w:V→ℝ)(s:(Stock.census V).Mode):
    WilsonOriginalCensusMount.aperture w s=(Poly.toll w (charged w s))⁻¹:=by
  simp only [WilsonOriginalCensusMount.aperture,charged,Poly.toll,← Finset.prod_inv_distrib,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v _
  by_cases paid:1 ≤ (w v)⁻¹
  · simp only [paid,if_true,max_eq_right paid]
  · simp only [paid,if_false,inv_one,max_eq_left (le_of_not_ge paid)]

theorem subset (w:V→ℝ)(s:(Stock.census V).Mode):(charged w s).val⊆s.val:=Finset.filter_subset .. 

include highBook lowBook in
theorem original (x:Wallet A)(z:Wallet A')(s:(marks).Mode):
    let a:=charged (w₂) s
    let b:=charged low.w s
    WilsonOriginalCensusMount.aperture (w₂) s ≤ ((Ω)^6)^a.val.card*tariff a ∧
      WilsonOriginalCensusMount.aperture low.w s ≤ tariff' b:=by
  intro a b
  have f:=highBook.wage x a
  have g:=lowBook.wage z b
  have one (time:ℝ) (insured:ℝ)(n:ℕ):1 ≤ (WilsonOriginalOccupiedSalary.debit time insured)^n:=
    one_le_pow₀ (le_max_left ..)
  have hi₀:1 ≤ tariff a * Poly.toll high.w a:=by simpa only [highBook.radius x] using (one _ _ _).trans f
  have lo₀:1 ≤ tariff' b * Poly.toll low.w b:=by simpa only [lowBook.radius z] using (one _ _ _).trans g
  have h:(Poly.toll high.w a)⁻¹ ≤ tariff a:=by simpa only [one_div] using (div_le_iff₀ (Poly.worth high.salary.positive a)).mpr hi₀
  have l:(Poly.toll low.w b)⁻¹ ≤ tariff' b:=by simpa only [one_div] using (div_le_iff₀ (Poly.worth low.salary.positive b)).mpr lo₀
  rw [selected (w₂) s,selected low.w s]
  refine ⟨?_,l⟩
  change (Poly.toll (w₂) a)⁻¹ ≤ _
  have restored:(Poly.toll (w₂) a)⁻¹=((Ω)^6)^a.val.card*(Poly.toll high.w a)⁻¹:=by
    simp only [Stoop.radius,Poly.toll,div_eq_inv_mul,Finset.prod_mul_distrib,Finset.prod_const,mul_inv,inv_pow,inv_inv]
  rw [restored]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end YM.Integration.WilsonOriginalCensusAperture
end
