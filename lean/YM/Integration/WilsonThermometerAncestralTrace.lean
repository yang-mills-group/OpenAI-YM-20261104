import YM.Integration.WilsonReceivedFirstTraceLocalized
import YM.Integration.WilsonThermometerAppointedDetector

/-! Original nonbare descent of all seven graded physical faces with a fixed top
cutoff. The upper receipt is the full physical joint post and its own declaration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralTrace
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

theorem same (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {j:ℕ} (jt:j≤t) :
    arr j jt = faces (jt.trans_lt top) :=by
  induction jt using Nat.decreasingInduction with
  | self =>exact WilsonReceivedCloseHistory.head (N:=N) R WilsonThermometerCourseHearing.disks (faces top)
  | of_succ l lt hyp =>
    rw [←WilsonReceivedCloseHistory.adjacent (N:=N) R WilsonThermometerCourseHearing.disks (faces top) lt,hyp]
    exact WilsonThermometerTestedReturn.push R A simple (show l+1<N by omega) o refs

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

def Reached (row:post t mt (faces top)) (rowCount:Countable row.inputIndex) (q:ℕ) (ε:ℝ) {j:ℕ} (mj:m≤j) (jt:j≤t) (L:post j mj (faces (jt.trans_lt top))) : Prop :=
  ∃P:post j mj (arr j jt),∃c:Countable P.inputIndex,
    (WilsonReceivedFirstTrace.Chain R hk D tab π Γ Ψ books ahead
  WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats W mt (faces top) row rowCount top q ε j mj (Nat.lt_of_le_of_lt jt top) (arr j jt) P c) ∧ HEq L P ∧ HEq L.input P.input ∧ HEq L.output P.output

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N)
    (path:PlanV.Path D R.alloy tab (Burn.horizon k) N m π Γ)
    (pass:Pass D tab R.alloy R.kit) (month:Scholar.Month R.rolls D tab R.alloy.delay)
    (fits:order≤Burn.horizon k+1) (packed:order+shelf≤Burn.horizon k+2) (q:ℕ) {ε:ℝ}
    (deep:2*q+8≤order) (aged:q+3≤3*k+2) (ep:0<ε) (unit:ε≤1) {j:ℕ}
    (late:WilsonReceivedMeasuredStampPrice.opening R W.simple q order k deep aged ep ≤ j+1)
    (small:∀l,j≤l→l≤N→0<g l ∧ g l≤1)
    (mj:m≤j) (jt:j≤t) :
    ∃L:post j mj (faces (jt.trans_lt top)), Reached R simple A top o hk D tab π Γ Ψ books ahead order
      shelf seats W mt inlet counted q ε mj jt L ∧
      L.rent ≤ inlet.rent+∑l∈Ico j t,ε*(g (l+2))^q ∧
      ∃d:ℝ,1≤d ∧ d≤roof j ∧ ∀v,L.w v=inlet.w v/d :=by
  obtain ⟨P,c,tr,rented⟩ := WilsonReceivedFirstTrace.from_date R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats
    W mt (faces top) inlet counted top q ε j path pass month fits packed deep aged ep unit late small j jt mj le_rfl
  have trail:=tr.trail
  obtain ⟨_,d,one,cap,issued⟩:=trail.wallet
  obtain ⟨L,samePost,wages,rent,_,_,sameIn,sameOut⟩:=
    WilsonThermometerHeldSource.actual R A simple (jt.trans_lt top) o hk D tab π Γ Ψ books ahead order shelf seats
      mj (arr j jt) P (same R simple A top o refs jt)
  refine ⟨L,⟨P,c,tr,samePost,sameIn,sameOut⟩,rent.le.trans rented,d,one,cap,fun v=>?_⟩
  rw [wages]
  exact issued v

end YM.Integration.WilsonThermometerAncestralTrace
