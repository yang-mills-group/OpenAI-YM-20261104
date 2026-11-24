import YM.Integration.WilsonOriginalCensusAperture
import YM.Integration.WilsonOriginalCensusFilingIncome
import YM.Integration.WilsonEmittedOriginalCalendar
import YM.Integration.WilsonOriginalCensusBookedCash
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
namespace YM.Integration.WilsonOriginalCensusPostedWages
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


local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "H₁" => R.alloy.B.a.clock.hatBeta j
local notation "nh" => ((∑v:V,grades v)+1+5)*Fintype.card V
local notation "nl" => ((∑v:V,grades' v)+1+5)*Fintype.card V
local notation "D₀" => max (nh) (nl)

def debit (depth:ℕ)(earned:V→ℕ)(s:(Stock.census V).Mode):ℕ:=6*s.val.card+depth+(∑v∈s.val,earned v)

private theorem toll {t:ℝ}(_hi:1 ≤ t)(bill:V→ℝ){a:V→ℕ}(nn:∀v,0 ≤ bill v)(grant:∀v,bill v ≤ t^(a v))
    (s:(Stock.census V).Mode):Poly.toll bill s ≤ t^(∑v∈s.val,a v):=by
  rw [Poly.toll,←Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun i _=>nn i) (fun i _=>grant i)

include highBook lowBook simple in
theorem original (x:Wallet A)(z:Wallet A')(s:(marks).Mode)
    (entered entered':V→ℝ)(charges:V→ℕ)(nn:∀v,0 ≤ entered v)(nn':∀v,0 ≤ entered' v)
    (upper:∀t,tariff t ≤ H^(nh)*Poly.toll entered t)(lower:∀t,tariff' t ≤ H₁^(nl)*Poly.toll entered' t)
    (fund:∀v,entered v ≤ H^(charges v))(fund':∀v,entered' v ≤ H^(charges v))
    (late:(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1):
    let d:=debit D₀ charges s
    WilsonOriginalCensusMount.aperture (w₂) s ≤ H^d ∧
    WilsonOriginalCensusMount.aperture low.w s ≤ H^d ∧
    WilsonEmittedJoinedFares.cash s (wages) (fun a=>if a then -1 else 1) (costs) ≤ 2*H^(d+1):=by
  intro d
  have H0:1 ≤ H:=(R.alloy.B.a.fits.delayed (j+1)).le
  have Hpos:0 ≤ H:=zero_le_one.trans H0
  have earlier:0 ≤ H₁:=zero_le_one.trans (R.alloy.B.a.fits.delayed j).le
  have moves:H₁≤H:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le (Nat.le_succ j)
  have dollars:budgetR R (j+1)≤H:=(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose_spec (j+1) late
  have pot:0 ≤ (Ω):=zero_le_one.trans high.issued.Waffle.cool
  have purchase:(Ω)≤H:=high.issued.Beamwork.trans dollars
  have bills (t:(marks).Mode):tariff t ≤ H^(D₀+∑v∈t.val,charges v) ∧ tariff' t ≤ H^(D₀+∑v∈t.val,charges v):=by
    rw [pow_add]
    exact ⟨(upper t).trans (mul_le_mul (pow_le_pow_right₀ H0 (le_max_left ..))
      (toll H0 entered nn fund t) (Finset.prod_nonneg (fun u _=>nn u)) (pow_nonneg Hpos _)),
      (lower t).trans (mul_le_mul ((pow_le_pow_left₀ earlier moves _).trans (pow_le_pow_right₀ H0 (le_max_right ..)))
      (toll H0 entered' nn' fund' t) (Finset.prod_nonneg (fun u _=>nn' u)) (pow_nonneg Hpos _))⟩
  have leg {t:(marks).Mode}(sub:t.val⊆s.val):
      ((Ω)^6)^t.val.card*tariff t ≤ H^d ∧ tariff' t ≤ H^d:=by
    have sizes:=Finset.card_le_card sub
    have wage:=Finset.sum_le_sum_of_subset_of_nonneg (f:=charges) sub (fun _ _ _=>Nat.zero_le _)
    have raw:=pow_le_pow_left₀ pot purchase (6*t.val.card)
    rw [pow_mul,pow_mul] at raw
    have a:=mul_le_mul_of_nonneg_left (bills t).1 (by positivity:0 ≤ ((Ω)^6)^t.val.card)
    have b:=mul_le_mul_of_nonneg_right raw (pow_nonneg Hpos (D₀+∑v∈t.val,charges v))
    have combine:((H)^6)^t.val.card*H^(D₀+∑v∈t.val,charges v)=H^(6*t.val.card+(D₀+∑v∈t.val,charges v)):=by rw [pow_add _ (6*t.val.card) (D₀+∑v∈t.val,charges v),pow_mul _ 6 t.val.card]
    have power:6*t.val.card+(D₀+∑v∈t.val,charges v)≤d:=by dsimp only [d,debit];omega
    refine ⟨a.trans (b.trans (combine.le.trans (pow_le_pow_right₀ H0 power))),(bills t).2.trans (pow_le_pow_right₀ H0 ?_)⟩
    omega
  obtain ⟨old,young⟩:=WilsonOriginalCensusAperture.original R hk D Q π Γ Ψ books lo ahead
    A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw high low highBook lowBook x z s
  have cash:=WilsonOriginalCensusBookedCash.original R hk D Q π Γ Ψ books lo ahead
    A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw high low highBook lowBook x z s
    (fun a=>if a then -1 else 1)
  have full:=leg (t:=s) (Finset.Subset.refl _)
  have one:low.cost ≤ H:=(low.affordable.trans (inv_le_one_of_one_le₀ low.issued.Waffle.cool)).trans H0
  have highCash:=mul_le_mul full.1 dollars (zero_le_one.trans (budget_pos R)) (pow_nonneg Hpos _)
  have lowCash:=mul_le_mul full.2 one (budget_nonneg (low.salary.suggests 0)) (pow_nonneg Hpos _)
  norm_num only [Bool.false_eq_true,if_false,if_true,abs_one,abs_neg,one_mul] at cash
  refine ⟨old.trans (leg (WilsonOriginalCensusAperture.subset _ s)).1,
    young.trans (leg (WilsonOriginalCensusAperture.subset _ s)).2,cash.trans ?_⟩
  rw [pow_succ,two_mul]
  exact add_le_add highCash lowCash

end YM.Integration.WilsonOriginalCensusPostedWages
end
