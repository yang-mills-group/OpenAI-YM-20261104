import YM.Integration.WilsonThermometerAncestralLedger
import YM.Integration.WilsonThermometerAncestralCell
import YM.Integration.WilsonThermometerCenteredWeight
import YM.Integration.WilsonThermometerAncestralWallet
import YM.Integration.WilsonThermometerAncestralCalendar
import YM.Integration.WilsonReceivedFirstTraceRoster

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralNumbers
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

open OPE.Therm Pert.Asymptotics WilsonReceivedFirstTrace WilsonPositionThermometerGradedSource WilsonThermometerCourseHearing

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m t N per k:ℕ}
  (top:t<N) (o:Positions (Fin 3) (R.family.side N per))
local notation "faces" itr:max => WilsonThermometerCourseHearing.offered R A simple itr o
local notation "arr" j:max jt:max => WilsonReceivedCloseHistory.history (N:=N) R WilsonThermometerCourseHearing.disks (faces top) j jt
variable (hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (tab:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ→ℕ} (books:Mentor.Offices.Books D R.rolls tab φ) (ahead:Mentor.Forecast D R.rolls tab φ books)
  (order shelf seats:ℕ)
local notation "ages" => (fun v:Fin 3=>(grade v).val)
local notation "post" j:max mj:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D tab π Γ Ψ books
  ahead WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats j mj y
variable (W:Registration (m:=m) (N:=N) (k:=k) R D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks shelf seats)
  (mt:m≤t)
open WilsonThermometerAncestralTrace
local notation "place" j:max => WilsonReceivedFirstTrace.Position (m:=m) (N:=N) (per:=per) R hk D tab π Γ Ψ books ahead
  WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats j
local notation "edge" e:max j:max U:max L:max => WilsonReceivedFirstTrace.Adjacent R hk D tab π Γ Ψ books ahead
  WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats W
  e 1 j U L


open WilsonThermometerCenteredAlgebra WilsonThermometerAncestralRoster
local notation "B" => budgetR R
local notation "g" => regulatorRun R.family N per
local notation "headroom" mj:max L:max => Oak.expenseReal R hk D tab π Γ books mj
  (L).op (L).lesson ahead order shelf


open Laurent Stationary Comparison.RG02 Comparison.RG02.Order WilsonThermometerWeightedCapture
open Primitives.GCC.Anchor WilsonFiniteOrdinaryInverse
local notation "strip" => (∀ a k:ℕ,k ≤ a → ∀x:ℝ,R.alloy.delay.betaEntry a ≤ x →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹^2) ≤ x)
local notation "roster" j:max L:max => Air.craft (L).post.model (fun v=>((L).post.model v).paint fired) ages
  (π (j+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "J" => Stock.census (Fin 3)
local notation "sheet" j:max => R.family.path.levels.clock.op j per
local notation "base" j:max => Stationary.arm G (R.family.side j per) 1
local notation "program" j:max live:max => (RunFormalChain.fromRun R).step N j per live
local notation "budget₀" j:max => R.family.path.levels.budget j
/-- Evaluate the whole finite table on this actual member of the chronological list. -/
def Tested {j:ℕ} (L:place j) (l depth:ℕ) (H cap:ℝ) : Prop :=
  ∀(a:Stationary.Link G (R.family.side j per)) (z:ℝ),
      |z| ≤ |H| *(Real.log (R.family.path.levels.clock.hatBeta j))^depth*
        (((budget₀ j).B:ℝ)^2*(budget₀ j).threshold)/(g (j+1)) →
      (∀e,‖Exterior.collect G ((base j) a) e‖ ≤ cap*|z|) →
      let bank:=roster j L
      let Q:=Order.value (g (j+1):ℂ) (Order.ratio (PhysicalWilsonPeriodizedMaterial.reference R N j per L.cut ((base j) a) bank order))
      (∀(F₀:Forest (sheet j).ratio) (ξ:(sheet j).Choices),
        Order.value (g (j+1):ℂ) (Order.ratio (Bulk.Fk (program j L.cut) F₀ ξ bank ((base j) a) order))=Q) ∧
      Poly.price (fun v=>(g (j+1))*L.post.w v) (inverseMass Q) ≤ fee J ∧
      (g (j+1))^(l+5)*(∑ s:(J).Mode,‖weight Q s‖/Poly.toll L.post.w s) ≤ fee J

include W in
theorem at_position {j:ℕ} (L:place j) (same:L.field=faces L.cut) (l:ℕ) (wallet:(g (j+1))^(l+2) ≤ Poly.toll L.post.w full)
    (weak:0<g (j+1) ∧ g (j+1) ≤ 1) (fit:k ≤ R.alloy.B.a.clock.J j)
    (fund:Volume.Fund D R.rolls tab φ books R.alloy.delay) (stripGrant:strip) (depth:ℕ) (H cap:ℝ) (hc:0 ≤ cap)
    (heard:(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ stripGrant order shelf
      k seats depth H cap hc)).choose ≤ j) : Tested R hk D tab π Γ Ψ books ahead order shelf seats L l depth H cap :=by
  rcases L with ⟨floor,live,observed,P,c⟩
  change observed=offered R A simple live o at same
  subst observed
  intro a z rent inside bank Q
  have datum (F₀:Forest (sheet j).ratio) (ξ:(sheet j).Choices) :
      Order.value (g (j+1):ℂ) (Order.ratio (Bulk.Fk (program j live) F₀ ξ bank ((base j) a) order))=Q := by
    exact congrArg (fun M=>Order.value (g (j+1):ℂ) (Order.ratio M))
      (WilsonThermometerCenteredMaterial.posted R A simple hk D tab π Γ Ψ books floor live ahead order shelf
        seats o P ((base j) a) F₀ ξ)
  let F₀:=WilsonCoeffUV.repeatF (sheet j)
  let ξ:=PhysicalWilsonPeriodizedProgram.branch (sheet j)
  have bill:=(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ stripGrant order shelf
    k seats depth H cap hc)).choose_spec j heard A hk fit tab π Γ Ψ W.course books W.scroll W.chamber fund
      floor live o ahead P a z rent inside F₀ ξ
  have inverse:Poly.price (fun v=>(g (j+1))*P.w v) (inverseMass Q) ≤ fee J := (datum F₀ ξ) ▸ bill.1
  exact ⟨datum,inverse,by simpa only [show (3+(l+2))=l+5 by omega] using
    WilsonThermometerCenteredWeight.original Q P.w P.issued.earning.positive weak.1 weak.2 (l+2) wallet inverse⟩

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {i:ℕ} (mi:m ≤ i) (it:i ≤ t)
    (atCut:post i mi (faces (it.trans_lt top))) (found:Reached R simple A top o hk D tab π Γ Ψ
      books ahead order shelf seats W mt inlet counted (q+2) 1 mi it atCut)
    (degree l:ℕ) {price:ℝ} (cap:0 ≤ price)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (days:((t-i:ℕ):ℝ) ≤ price*(Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta i)))^degree)
    (weak:(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose ≤ i)
    (booked:(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple (degree+1) seats q l cap)).choose ≤ i)
    (oldRent:inlet.rent ≤ (g t)^(q+2)) (start:(g t)^l ≤ Poly.toll inlet.w full)
    (fit:k ≤ R.alloy.B.a.clock.J i) (fund:Volume.Fund D R.rolls tab φ books R.alloy.delay) (stripGrant:strip) (depth:ℕ) (H cap₀:ℝ) (hc:0 ≤ cap₀)
    (heard:(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ stripGrant order shelf
      k seats depth H cap₀ hc)).choose ≤ i) :
    ∃ f:(j:ℕ) → Option (place j),
      f t = some (⟨mt,top,faces top,inlet,counted⟩ : place t) ∧
      (∃Z:place i,f i=some Z ∧ HEq atCut Z.post ∧ HEq atCut.input Z.post.input ∧
        HEq atCut.output Z.post.output) ∧
      ∀j,i ≤ j → j<t → ∃(U:place (j+1)) (L:place j), f (j+1)=some U ∧ f j=some L ∧
        edge (q+2) j U L ∧ U.field=faces U.cut ∧ L.field=faces L.cut ∧
        (8*(headroom L.floor L.post)^L.post.op.count)*L.post.rent ≤ (1/4)*(g (j+1))^q ∧
        (g (j+1))^(l+2) ≤ Poly.toll L.post.w full ∧
        Tested R hk D tab π Γ Ψ books ahead order shelf seats L l depth H cap₀ :=by
  obtain ⟨f,first,last,links⟩:=WilsonThermometerAncestralLedger.original R simple A top o hk D tab π Γ Ψ
    books ahead order shelf seats W mt inlet counted q refs mi it atCut found degree l cap slow days weak booked
    oldRent start
  refine ⟨f,first,last,?_⟩
  intro j ij jt
  obtain ⟨U,L,vU,vL,edge₀,fine,coarse,bill,aperture⟩:=links j ij jt
  have gp:=(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose_spec i weak
    N per (j+1) (by omega) (by omega)
  have price:=at_position R simple A o hk D tab π Γ Ψ books ahead order shelf seats W L coarse l aperture gp
    (fit.trans (R.alloy.B.a.fits.mono ij)) fund stripGrant depth H cap₀ hc (heard.trans ij)
  exact ⟨U,L,vU,vL,edge₀,fine,coarse,bill,aperture,price⟩

end YM.Integration.WilsonThermometerAncestralNumbers
