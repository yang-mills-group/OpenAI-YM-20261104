import YM.Integration.WilsonThermometerAncestralRoster
import YM.Integration.WilsonThermometerAncestralWallet
import YM.Integration.WilsonThermometerAncestralCalendar
import YM.Integration.WilsonReceivedFirstTraceRoster

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralLedger
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

theorem rent (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ)
    {i:ℕ} (small:∀k,i ≤ k → k ≤ N → 0 ≤ g k) {j:ℕ} {mj:m ≤ j} {live:j<N}
    {read:Wallet WilsonThermometerCourseHearing.disks → Config G (R.family.side (j+1) per) → Poly (Stock.census (Fin 3))}
    {P:post j mj read} {c:Countable P.inputIndex} (trace:Chain R hk D tab π Γ Ψ books ahead
      WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats W
      mt (faces top) inlet counted top (q+2) 1 j mj live read P c) : i ≤ j →
      P.rent ≤ inlet.rent+∑l∈Ico j t,(g (l+2))^(q+2) :=by
  induction trace with
  | start =>simp
  | @step j mj cut field U c L h C E prev paid ih =>
    intro ij
    have before:=ih (by omega)
    have jt:j<t:=(Nat.lt_succ_self j).trans_le (Chain.level R hk D tab π Γ Ψ books ahead
      WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats W
      mt (faces top) inlet counted top (q+2) 1 prev)
    have debt:0 ≤ (g (j+2))^(q+2):=pow_nonneg (small _ (by omega) (by omega)) _
    have received : L.rent ≤ U.rent+(g (j+2))^(q+2) :=by
      rw [paid.rent]
      simp only [one_mul] at *
      apply max_le
      · exact (mul_le_mul_of_nonneg_left paid.available (inv_nonneg.mpr (zero_le_one.trans paid.positive))).trans
          (mul_le_of_le_one_left (U.active.le.trans (le_add_of_nonneg_right debt)) (inv_le_one_of_one_le₀ paid.positive))
      · exact le_add_of_nonneg_left U.active.le
    rw [←insert_Ico_add_one_left_eq_Ico jt,sum_insert (by simp)]
    linarith only [received,before]

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {i:ℕ} (mi:m ≤ i) (it:i ≤ t)
    (atCut:post i mi (faces (it.trans_lt top))) (found:Reached R simple A top o hk D tab π Γ Ψ
      books ahead order shelf seats W mt inlet counted (q+2) 1 mi it atCut)
    (degree l:ℕ) {price:ℝ} (cap:0 ≤ price)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (days:((t-i:ℕ):ℝ) ≤ price*(Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta i)))^degree)
    (weak:(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose ≤ i)
    (booked:(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple (degree+1) seats q l cap)).choose ≤ i)
    (oldRent:inlet.rent ≤ (g t)^(q+2)) (start:(g t)^l ≤ Poly.toll inlet.w full) :
    ∃ f:(j:ℕ) → Option (place j),
      f t = some (⟨mt,top,faces top,inlet,counted⟩ : place t) ∧
      (∃Z:place i,f i=some Z ∧ HEq atCut Z.post ∧ HEq atCut.input Z.post.input ∧
        HEq atCut.output Z.post.output) ∧
      ∀j,i ≤ j → j<t → ∃(U:place (j+1)) (L:place j), f (j+1)=some U ∧ f j=some L ∧
        edge (q+2) j U L ∧ U.field=faces U.cut ∧ L.field=faces L.cut ∧
        (8*(headroom L.floor L.post)^L.post.op.count)*L.post.rent ≤ (1/4)*(g (j+1))^q ∧
        (g (j+1))^(l+2) ≤ Poly.toll L.post.w full :=by
  obtain ⟨P,c,chain,hP,hIn,hOut⟩:=found
  obtain ⟨f,first,last,edges⟩:=Chain.roster R hk D tab π Γ Ψ books ahead
    WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats
    W mt (faces top) inlet counted top (q+2) 1 chain
  refine ⟨f,first,⟨_,last,hP,hIn,hOut⟩,?_⟩
  have small:∀k,i ≤ k → k ≤ N → 0 ≤ g k :=fun k ik kN =>
    ((eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose_spec i weak N per k ik kN).1.le
  have closed:=WilsonThermometerAncestralCalendar.counted R simple slow degree cap it days
  have stages:∀j∈Ico i t,2 ≤ B j :=by
    intro j hj
    obtain ⟨_,L,_⟩:=edges j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2
    have four:4 ≤ headroom L.floor L.post := MintClock.Page.roofers ..
    exact (show 2 ≤ headroom L.floor L.post by linarith only [four]).trans L.post.issued.Beamwork
  intro j ij jt
  obtain ⟨U,L,atU,atL,receipt,above,below⟩:=edges j ij jt
  obtain ⟨_,d,one,ceiling,wage⟩:=(Chain.trail R hk D tab π Γ Ψ books ahead
    WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats
    W mt (faces top) inlet counted top (q+2) 1 below).wallet
  have fullPrice : Poly.toll L.post.w full = Poly.toll inlet.w full/d^3 :=by
    rw [show L.post.w=(fun v=>inlet.w v/d) from funext wage]
    simp [Poly.toll,full,prod_div_distrib]
  have charge:=rent R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted q small below ij
  have bill:=(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple (degree+1) seats q l cap)).choose_spec
    j (booked.trans ij) t N per i ij jt top closed d (headroom L.floor L.post) inlet.rent L.post.rent
    (Poly.toll inlet.w full) (Poly.toll L.post.w full) L.post.op.count one ceiling
    (zero_le_one.trans L.post.issued.Waffle.cool) L.post.issued.Beamwork L.post.capacity.le inlet.active.le oldRent
    L.post.active.le charge (fun v hv=>stages v (mem_Ico.mpr ⟨ij.trans (mem_Ico.mp hv).1,(mem_Ico.mp hv).2⟩)) start fullPrice
  exact ⟨U,L,atU,atL,receipt,
    named R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted q refs above,
    named R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted q refs below,bill⟩

end YM.Integration.WilsonThermometerAncestralLedger
