import YM.Integration.WilsonThermometerAncestralTrace
import YM.Integration.WilsonThermometerAncestralFunds
import YM.Integration.WilsonThermometerCenteredAlgebra

/-! Price the single marked gallery along the original two nonbare post operations
and the booked close interval preceding them. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralWallet
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
local notation "B" => budgetR R
local notation "roof" j:max => ∏ l∈Ico j t,(B l)^2*(B (l+1))^7
local notation "g" => regulatorRun R.family N per

open WilsonThermometerAncestralTrace WilsonThermometerCenteredAlgebra
local notation "headroom" mj:max L:max => Oak.expenseReal R hk D tab π Γ books mj
  (L).op (L).lesson ahead order shelf

private theorem stages (row:post t mt (faces top)) (rowCount:Countable row.inputIndex)
    {q:ℕ} {ε:ℝ} {j:ℕ} {mj:m ≤ j} {live:j<N}
    {y:Wallet WilsonThermometerCourseHearing.disks → Config G (R.family.side (j+1) per) → Poly (Stock.census (Fin 3))}
    {P:post j mj y} {c:Countable P.inputIndex}
    (tr:WilsonReceivedFirstTrace.Chain R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks
      WilsonThermometerCourseHearing.sectors ages order shelf seats W mt (faces top) row rowCount top q ε
      j mj live y P c) : ∀l∈Ico j t,2 ≤ B l := by
  induction tr with
  | start =>simp
  | @step j mj live y upper prev L h C E before paid stages =>
    have four : 4 ≤ headroom mj L := MintClock.Page.roofers ..
    have funded : 2 ≤ B j := (show 2 ≤ headroom mj L by linarith only [four]).trans L.issued.Beamwork
    intro l hl
    rcases eq_or_lt_of_le (mem_Ico.mp hl).1 with rfl|after
    · exact funded
    · exact stages l (mem_Ico.mpr ⟨after,(mem_Ico.mp hl).2⟩)

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N)
    (path:PlanV.Path D R.alloy tab (Burn.horizon k) N m π Γ)
    (pass:Pass D tab R.alloy R.kit) (month:Scholar.Month R.rolls D tab R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (packed:order+shelf ≤ Burn.horizon k+2)
    (q l degree:ℕ) {price:ℝ} (cap:0 ≤ price) (deep:2*(q+2)+8 ≤ order) (aged:q+2+3 ≤ 3*k+2) {i:ℕ}
    (late:WilsonReceivedMeasuredStampPrice.opening R W.simple (q+2) order k deep aged zero_lt_one ≤ i+1)
    (small:∀j,i ≤ j → j ≤ N → 0<g j ∧ g j ≤ 1) (mi:m ≤ i) (both:i+2 ≤ t)
    (close:PaceR.Close R degree price i t)
    (booked:(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple degree seats q l cap)).choose ≤ i)
    (oldRent:inlet.rent ≤ (g t)^(q+2)) (start:(g t)^l ≤ Poly.toll inlet.w full) :
    ∃L:post i mi (faces (show i<N by omega)), Reached R simple A top o hk D tab π Γ Ψ books ahead order shelf
      seats W mt inlet counted (q+2) 1 mi (show i ≤ t by omega) L ∧
      (8*(headroom mi L)^L.op.count)*L.rent ≤ (1/4)*(g (i+1))^q ∧
      (g (i+1))^(l+2) ≤ Poly.toll L.w full := by
  obtain ⟨L,reached,rented,d,one,ceiling,wage⟩:=
    WilsonThermometerAncestralTrace.original R simple A top o hk D tab π Γ Ψ books ahead order shelf seats
      W mt inlet counted refs path pass month fits packed (q+2) deep aged zero_lt_one le_rfl late small mi (by omega)
  have budget : ∀j∈Ico i t,2 ≤ B j := by
    obtain ⟨L₁,c,tr,_,_,_⟩:=reached
    exact stages R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted tr
  have fullPrice : Poly.toll L.w full = Poly.toll inlet.w full/d^3 :=by
    rw [show L.w=(fun v=>inlet.w v/d) from funext wage]
    simp [Poly.toll,full,prod_div_distrib]
  have wages:=(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple degree seats q l cap)).choose_spec
    i booked t N per i le_rfl (by omega) top close d (headroom mi L) inlet.rent L.rent
      (Poly.toll inlet.w full) (Poly.toll L.w full) L.op.count one ceiling
      (zero_le_one.trans L.issued.Waffle.cool) L.issued.Beamwork L.capacity.le inlet.active.le oldRent L.active.le
      (by simpa only [one_mul] using rented) budget start fullPrice
  exact ⟨L,reached,wages⟩

end YM.Integration.WilsonThermometerAncestralWallet
