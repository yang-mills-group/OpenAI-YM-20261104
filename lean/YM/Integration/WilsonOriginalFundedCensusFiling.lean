import YM.Integration.WilsonOriginalPhysicalAngularFiling
import YM.Integration.WilsonOriginalCensusPostedWages
import YM.Integration.WilsonOriginalCensusFiledProbe
import YM.Integration.WilsonOriginalCensusFilingAccounts
import YM.Integration.WilsonOriginalCensusTariff
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
namespace YM.Integration.WilsonOriginalFundedCensusFiling
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
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀i,RG.Rep G (R.family.side i per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ) (lo:m ≤ j) (cut:j+1 < N)
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
local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "H₁" => R.alloy.B.a.clock.hatBeta j
local notation "nh" => ((∑v:V,grades v)+1+5)*Fintype.card V
local notation "nl" => ((∑v:V,grades' v)+1+5)*Fintype.card V
local notation "fee" c:max t:max => WilsonOriginalCensusPostedWages.debit (max (nh) (nl)) c t
include simple course cut lowBook in
theorem original (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J (j+1))
    (load:high.op.count ≤ Burn.horizon k+2)(q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(depth:order' ≤ R.alloy.B.a.clock.J (j+1))
    (shelved:shelf' ≤ R.alloy.B.a.clock.J j) (slots:low.op.count ≤ Burn.horizon k+2)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1)
    (s:(marks).Mode)(x:Wallet A)(z:Wallet A')
    (h:ℕ)(tube:LinkTube G)(front:Hot (marks)→V)(mem:∀t,front t∈t.val.val)

    (placed:((vac).p.supportExponent+2)*((vac).p.B:ℝ)⁻¹ ≤ (σ)/2)
    (width:0<σ)(entered entered':V→ℝ)(charges:V→ℕ)(nn:∀v,0 ≤ entered v)(nn':∀v,0 ≤ entered' v)
    (upper:∀t,tariff t ≤ H^(nh)*Poly.toll entered t)(lower:∀t,tariff' t ≤ H₁^(nl)*Poly.toll entered' t)
    (fund:∀v,entered v ≤ H^(charges v))(fund':∀v,entered' v ≤ H^(charges v))
    (income:(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1)
    (target:ℕ){δ:ℝ}(dp:0 ≤ δ)(read:∀t:Hot (marks),t.val.val⊆s.val→
      WilsonOriginalCensusFiledProbe.Reading (both) (degrees) (WilsonOriginalCensusAngularFace.tests x z) (vac).p
        (fun _=>σ) (orders) (gc) t (front t) ((home) (front t)) tube (2*((fee charges t.val)+1))
        target (2*((2:ℝ)^((fee charges t.val)+1))) δ):
    let d:=fee charges s
    ∃F:WilsonOriginalMountedRegular.Filing R (vac) (highBook.row x) (lowerLaw z) s,
      F.w=(w₂) ∧ F.w'=low.w ∧ F.α=(vac).p.supportExponent+1+1 ∧ F.W ≤ H^d ∧ F.W' ≤ H^d ∧ F.regular ≤ H^2 ∧
      F.rent=high.rent+ε*(Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta)^q ∧
      F.gross ≤ (2^(order+shelf+1)/(gc)^((∑v:V,grades v)+1))*H^2 ∧
      F.nextGross ≤ (2^(order'+shelf'+1)/(gc)^((∑v:V,grades' v)+1))*H ∧
      F.M=max (F.W*(F.regular+F.rent)) (F.W'*F.nextGross) ∧ F.h=h ∧ F.δ=δ ∧ (Ω) ≤ H:=by
  intro d
  have booked (t:(marks).Mode):=WilsonOriginalCensusPostedWages.original R simple hk D Q π Γ Ψ books lo ahead
    A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw high low highBook lowBook
    x z t entered entered' charges nn nn' upper lower fund fund' income
  have posH:0<H:=zero_lt_one.trans (R.alloy.B.a.fits.delayed (j+1))
  have dollars:budgetR R (j+1)≤H:=(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose_spec (j+1) income
  have earned:0 ≤ budgetR R (j+1):=zero_le_one.trans (budget_pos R)
  have allowance:0<(Ω)^6:=pow_pos (zero_lt_one.trans_le high.issued.Waffle.cool) 6
  have entry:=course.1.walk (j+1) (Nat.le_succ_of_le lo) cut.le
  have thermal:H/2 ≤ (vac).beta:=by
    rw [entry.beta]
    exact (R.makes.wilson.represents N per (j+1) cut.le).band.1
  have bp:0<(vac).beta:=lt_of_lt_of_le (by positivity) thermal
  have gp:0<(gc):=inv_pos.mpr (Real.sqrt_pos.mpr bp)
  have positive (b:Bool):∀v,0<(wages) b v:=by
    cases b
    · exact fun v=>div_pos (high.salary.positive v) allowance
    · exact low.salary.positive
  have funds (b:Bool):0 ≤ (costs) b:=by
    cases b
    · exact earned
    · exact budget_nonneg (low.salary.suggests 0)
  have tests (t:Hot (marks))(ht:t.val.val⊆s.val):=by
    let fin:=fee charges t.val
    have current:=WilsonOriginalCensusTariff.measured gp posH bp thermal rfl (fin+1)
    have paid:WilsonEmittedJoinedFares.cash t.val (wages) (fun a=>if a then -1 else 1) (costs) ≤
        (2*((2:ℝ)^(fin+1)))*((gc)^(2*(fin+1)))⁻¹:=by
      rw [mul_assoc]
      exact (booked t.val).2.2.trans (mul_le_mul_of_nonneg_left current (by norm_num))
    exact WilsonOriginalCensusFiledProbe.purchased (both) (wages) (degrees) (WilsonOriginalCensusAngularFace.tests x z)
      (vac).p (fun _=>σ) (costs) (orders) (gc) t (front t) ((home) (front t)) tube _ _ _ _
      (read t ht) (fun _=>width) funds positive (by positivity) paid
  have block:=WilsonOriginalPhysicalAngularFiling.original R simple hk D Q π Γ Ψ course books lo cut ahead
    A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw high low highBook lowBook
    way pass month hospital fits narrow load q deep aged ep late warm depth shelved slots halo s x z h tube front mem
    placed dp tests
  let sale:=WilsonOriginalCensusRestamp.original R hk D Q π Γ Ψ course books (Nat.le_succ_of_le lo) cut ahead
    A K grades order shelf seats upperLaw high simple way pass month hospital fits narrow load q deep aged ep late
  obtain ⟨F,w,w',alpha,ap,ap',reg,rent,gross,later,M,crop,quote,_⟩:=block
  have head₀:0 ≤ sale.choose:=budget_nonneg (sale.choose_spec.2.1.suggests 0)
  have earned₁:Invoice.price (vac).p (fig).mist (order+shelf+1) high.op.count
      ((vac).p.supportExponent+1+1) (fig).limitC G ≤ budgetR R (j+1):=high.issued.Waffle.quote.trans high.issued.Beamwork
  have salaried:F.regular ≤ H^2:=by
    rw [reg,pow_two]
    exact mul_le_mul (earned₁.trans dollars) (sale.choose_spec.1.trans dollars) head₀ posH.le
  have pupil:=WilsonOriginalCensusFilingIncome.lower R hk D Q π Γ Ψ course books lo cut ahead A' K' grades'
    order' shelf' seats' lowerLaw low warm depth shelved slots
  have b₂:=mul_le_mul pupil (low.affordable.trans (inv_le_one_of_one_le₀ low.issued.Waffle.cool))
    (budget_nonneg (low.salary.suggests 0)) posH.le
  rw [mul_one] at b₂
  refine ⟨F,w,w',alpha,ap.trans_le (booked s).1,ap'.trans_le (booked s).2.1,salaried,rent,?_,?_,M,
    crop,quote,high.issued.Beamwork.trans dollars⟩
  · rw [gross]
    apply mul_le_mul_of_nonneg_left (reg.symm.trans_le salaried)
    positivity
  · rw [later]
    exact mul_le_mul_of_nonneg_left b₂ (by positivity)

end YM.Integration.WilsonOriginalFundedCensusFiling
end
