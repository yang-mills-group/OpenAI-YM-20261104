import YM.Integration.WilsonThermometerAncestralTrace
import YM.Integration.WilsonReceivedFirstTraceRoster

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralRoster
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

theorem named (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {j:ℕ} {mj:m ≤ j} {live:j<N}
    {read:Wallet WilsonThermometerCourseHearing.disks → Config G (R.family.side (j+1) per) → Poly (Stock.census (Fin 3))}
    {P:post j mj read} {c:Countable P.inputIndex} (trace:Chain R hk D tab π Γ Ψ books ahead
      WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats W
      mt (faces top) inlet counted top (q+2) 1 j mj live read P c) : read=faces live :=by
  induction trace with
  | start =>rfl
  | @step j mj cut field U c L h C E previous receipt ih =>
    rw [ih]
    exact WilsonThermometerTestedReturn.push R A simple cut o refs

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {i:ℕ} (mi:m ≤ i) (it:i ≤ t)
    (atCut:post i mi (faces (it.trans_lt top))) (found:Reached R simple A top o hk D tab π Γ Ψ
      books ahead order shelf seats W mt inlet counted (q+2) 1 mi it atCut) :
    ∃ f:(j:ℕ) → Option (place j),
      f t = some (⟨mt,top,faces top,inlet,counted⟩ : place t) ∧
      (∃Z:place i,f i=some Z ∧ HEq atCut Z.post ∧ HEq atCut.input Z.post.input ∧
        HEq atCut.output Z.post.output) ∧
      ∀j,i ≤ j → j<t → ∃(U:place (j+1)) (L:place j), f (j+1)=some U ∧ f j=some L ∧
        edge (q+2) j U L ∧ U.field=faces U.cut ∧ L.field=faces L.cut :=by
  obtain ⟨P,c,chain,hP,hIn,hOut⟩:=found
  obtain ⟨f,first,last,edges⟩:=Chain.roster R hk D tab π Γ Ψ books ahead
    WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats
    W mt (faces top) inlet counted top (q+2) 1 chain
  refine ⟨f,first,⟨_,last,hP,hIn,hOut⟩,?_⟩
  intro j ij jt
  obtain ⟨U,L,atU,atL,receipt,above,below⟩:=edges j ij jt
  exact ⟨U,L,atU,atL,receipt,
    named R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted q refs above,
    named R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted q refs below⟩

end YM.Integration.WilsonThermometerAncestralRoster
