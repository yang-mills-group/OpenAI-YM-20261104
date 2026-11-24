import YM.Integration.WilsonOriginalFullRosterSoldHearing
import YM.Integration.WilsonOriginalFundedCensusFiling
import YM.Integration.WilsonOriginalFullRosterAccountHearing
import YM.Integration.WilsonOriginalFreshPrintedGross
import YM.Integration.WilsonOriginalFullRosterDatedOpening
import YM.Integration.WilsonOriginalFullRosterAngularPayment
import YM.Integration.WilsonOriginalCensusMountedPupils
import YM.Integration.WilsonOriginalPhysicalAngularFiling

/-! The shared-front return on the actual re-stamped original upper and the independently appointed lower. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterBookedHearing
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport
open scoped BigOperators Classical
/-- The finite whole-roster order is computed before either posted wallet or regulator. -/
def roof {V:Type}[Fintype V][DecidableEq V](d d':V→ℕ)(charges:V→ℕ)(target:ℕ):ℕ:=
  let both:=WilsonOriginalCensusAngularFace.sides d d'
  let workload:=max (((∑v,d v)+1+5)*Fintype.card V) (((∑v,d' v)+1+5)*Fintype.card V)
  Finset.univ.sup fun t:(Stock.census V).Mode=>WilsonOriginalCensusPhysicalLoad.head both t+
    WilsonOriginalCensusTariff.debit (2*(WilsonOriginalCensusPostedWages.debit workload charges t+1))
      (WilsonOriginalCensusPhysicalLoad.rank both)+target

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
local notation "strip" => WilsonEmittedCompactTariff.strip (σ)
local notation "count" => fun _ : Bool => Fintype.card V
local notation "rank" => fun _ : Bool => WilsonOriginalCensusPhysicalLoad.rank (degrees)
open Comparison.Density Comparison.Density.Mirrors Comparison.RG02 Comparison.Density.Transport AnalyticBridge.SectorAffine.Offset
open WilsonOriginalFullRosterAngularReturn
local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "H₁" => R.alloy.B.a.clock.hatBeta j
local notation "nh" => ((∑v:V,grades v)+1+5)*Fintype.card V
local notation "nl" => ((∑v:V,grades' v)+1+5)*Fintype.card V
local notation "fee" c:max t:max => WilsonOriginalCensusPostedWages.debit (max (nh) (nl)) c t
include simple course cut highBook lowBook in
theorem original (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J (j+1))
    (load:high.op.count ≤ Burn.horizon k+2)(q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1)
    (child:∀v,low.passport.origin v=(home) v)
    (placed:((vac).p.supportExponent+2)*((vac).p.B:ℝ)⁻¹ ≤ (σ)/2)
    (s:(marks).Mode)(x:Wallet A)(z:Wallet A')(tube:LinkTube G)
    (front:Multi.Hot (marks)→V)(mem:∀t,front t∈t.val.val){δ:ℝ}
    (width:0<σ)(entered entered':V→ℝ)(charges:V→ℕ)(nn:∀v,0 ≤ entered v)(nn':∀v,0 ≤ entered' v)
    (upper:∀t,tariff t ≤ H^(nh)*Poly.toll entered t)(lower:∀t,tariff' t ≤ H₁^(nl)*Poly.toll entered' t)
    (fund:∀v,entered v ≤ H^(charges v))(fund':∀v,entered' v ≤ H^(charges v))
    (income:(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1)
    (target:ℕ)(atStation:WilsonOriginalFullRosterDatedReturn.station R simple
      (roof grades grades' charges target) (Fintype.card V) ≤ j)(dp:0 ≤ δ)
    (read:∀t:Hot (marks),t.val.val⊆s.val→
      WilsonOriginalCensusFiledProbe.Reading (both) (degrees) (WilsonOriginalCensusAngularFace.tests x z) (vac).p
        (fun _=>σ) (orders) (gc) t (front t) ((home) (front t)) tube (2*((fee charges t.val)+1))
        target (2*((2:ℝ)^((fee charges t.val)+1))) δ)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(depth:order' ≤ R.alloy.B.a.clock.J (j+1))
    (shelved:shelf' ≤ R.alloy.B.a.clock.J j)(slots:low.op.count ≤ Burn.horizon k+2)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)(ticket:TicketP R.alloy R.kit D Q)
    (h p:ℕ){tol:ℝ}(tp:0<tol)(mature:WilsonCenteredCaptureClock.first R simple ≤ j+1)
    (failure:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose ≤ j+1)
    {i:ℕ}(floor:m ≤ i)(older:i ≤ j+1)(fixed:WilsonSingleHardRadius.first R simple ≤ i)
    (U:Config G (R.family.side i per))(clear:flags (Ψ i).p.threshold U=∅):
    let sale:=WilsonOriginalCensusRestamp.original R hk D Q π Γ Ψ course books (Nat.le_succ_of_le lo) cut ahead
      A K grades order shelf seats upperLaw high simple way pass month hospital fits narrow load q deep aged ep late
    let reg:=Invoice.price (vac).p (fig).mist (order+shelf+1) high.op.count ((vac).p.supportExponent+1+1)
      (fig).limitC G*sale.choose
    let χ:=R.alloy.B.a.clock.hatBeta (j+1)
    let other:=((2:ℝ)^(order'+shelf'+1)/(gc)^((∑v:V,grades' v)+1))*
      (Invoice.price (vac).p (MintClock.Page.temperature G 1 χ) (order'+shelf'+1) low.op.count
        ((vac).p.supportExponent+1) ((σ)/4) G*low.cost)
    let rent:=high.rent+ε*(Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta)^q
    let gross:=((2:ℝ)^(order+shelf+1)/(gc)^((∑ v:V,grades v)+1))*reg
    let W:=WilsonOriginalCensusMount.aperture (w₂) s
    let W':=WilsonOriginalCensusMount.aperture low.w s
    let M:=max (W*(reg+rent)) (W'*other)
    let span:=max (vac).p.B (reach (vac).p.B h)
    (carried).hard=high.output.hard ∧
      (∀a,LocalComparison.actualPush R.family N per (j+1) (upperLaw a)=
        (Tint.Patrol.picture (stamped) (carried)).density a) ∧
      ‖WilsonOriginalOccupiedJointEdge.ordinary R (marks) Ψ (N:=N) older (highBook.row x) (lowerLaw z) s U‖ ≤
        WilsonOriginalOrdinaryFlatHulls.change s M (W*rent+W*((Real.exp (((vac).p.supportExponent+1+1)*h))⁻¹*gross)+δ)+
          (if i=j+1 then 0 else (2*WilsonOriginalOrdinaryFlatHulls.cost s M)*((s.val.card*(span+span+1)^4:ℕ):ℝ)*
            (4*Real.exp ((vac).p.supportExponent+2))*tol/χ^p*(Real.exp (WilsonOriginalDecoderSpring.bill
              (R.family.path.levels.clock.op i per) (R.family.path.β N per (i+1)) U))^2):=by
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
  have tests (t:Hot (marks))(ht:t.val.val⊆s.val):
      {a:Probe (both) (wages) (degrees) (WilsonOriginalCensusAngularFace.tests x z) (vac).p
        (fun _=>σ) (costs) (fun _=>strip) (orders) (count) (rank) (gc) t (front t) ((home) (front t))
        tube δ // a.T ≤ roof grades grades' charges target}:=by
    let fin:=fee charges t.val
    have current:=WilsonOriginalCensusTariff.measured gp posH bp thermal rfl (fin+1)
    have paid:WilsonEmittedJoinedFares.cash t.val (wages) (fun a=>if a then -1 else 1) (costs) ≤
        (2*((2:ℝ)^(fin+1)))*((gc)^(2*(fin+1)))⁻¹:=by
      rw [mul_assoc]
      exact (booked t.val).2.2.trans (mul_le_mul_of_nonneg_left current (by norm_num))
    refine ⟨WilsonOriginalCensusFiledProbe.purchased (both) (wages) (degrees) (WilsonOriginalCensusAngularFace.tests x z)
      (vac).p (fun _=>σ) (costs) (orders) (gc) t (front t) ((home) (front t)) tube _ _ _ _
      (read t ht) (fun _=>width) funds positive (by positivity) paid,?_⟩
    apply Finset.le_sup (f:=fun u:(Stock.census V).Mode=>WilsonOriginalCensusPhysicalLoad.head (degrees) u+
      WilsonOriginalCensusTariff.debit (2*((fee charges u)+1)) (rank false)+target)
    exact Finset.mem_univ t.val
  exact WilsonOriginalFullRosterSoldHearing.original R simple hk D Q π Γ Ψ course books lo cut ahead
    A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw high low highBook lowBook
    way pass month hospital fits narrow load q deep aged ep late child placed s x z tube front mem
    (roof grades grades' charges target) atStation (fun t ht=>(tests t ht).val) (fun t ht=>(tests t ht).property) dp
    warm depth shelved slots halo section_ group ticket h p tp mature failure floor older fixed U clear

end YM.Integration.WilsonOriginalFullRosterBookedHearing
end
