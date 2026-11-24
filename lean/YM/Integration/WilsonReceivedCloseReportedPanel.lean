import YM.Integration.WilsonReceivedCloseReportedStation
import YM.Integration.WilsonReceivedCloseRefundedWindow

/-! The actual seven-face signed physical read on a checked two-transfer reporter and its copied program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseReportedPanel
open Pert.Asymptotics
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i+1)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+2)) (R.family.path.levels.clock.forcedAllowance (i+2)))
  (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (i+2) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
  (lesson:Lesson (N:=i+2) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+2) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+2))
local notation "M₀" => primitive R A (i+2) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+2)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self (i+1)) o

variable {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
  {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)

open FVA1Physical.TwoReset

local notation "E₁" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ₀)
local notation "w₁" => (fun _:Fin 3 => ((E₁)*(Ω₀))⁻¹)


local notation "x₀" => regulatorRun R.family (i+2) per (i+1)
local notation "U₀" => WilsonReceivedCloseReportedWallet.unit R
local notation "initial" => WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks
  (S₀) levels school.order school.horizon school.pieces (i+1) hi (head)
local notation "sale" S:max => WilsonReceivedCloseNamedWallet.Sold (N:=i+2) (b:=i+1) (V:=Fin 3) (X:=fun _=>ℂ) R hk D Q π Γ Ψ books ahead disks (S₀) levels
  school.order school.horizon school.pieces hi (head) S univ (U₀*(x₀⁻¹)^37)
local notation "faces" S:max q:max span:max H:max ac:max ε:max => WilsonReceivedCloseOrdinaryRoster.Served (N:=i+2) (b:=i+1) (V:=Fin 3) (X:=fun _=>ℂ) R hk D Q π Γ Ψ
  books ahead disks (S₀) levels school.order school.horizon school.pieces hi (head) S (Nat.lt_succ_self (i+1))
  span H ac univ 3 (U₀*(x₀⁻¹)^37) (x₀^(q+37*3+1+3)) (ε*x₀^q)
variable (protection:∀ x k:ℕ,k≤x→∀β:ℝ,R.alloy.delay.betaEntry x≤β→
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2)≤β)
  (q prec span degree:ℕ) (H angleCap cap ε:ℝ) (deep:2*(prec+1)+8 ≤ school.order) (aged:prec+4≤3*k+2)
  (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "window" => WilsonReceivedCloseStationCalendar.Ready R simple D φ protection levels k
  school.order school.horizon school.pieces 3 18 q prec span degree (U₀) H angleCap cap ε
  (WilsonReceivedCloseReportedWallet.covers R) deep aged hp cp ep m (i+1)
variable (path:PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ)
  (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
  (volume:Volume.Fund D R.rolls Q φ books R.alloy.delay) (closeDates:PaceR.Close R degree cap m (i+1))
  (narrow:school.horizon ≤ R.alloy.B.a.clock.J m) (enrolled:k ≤ R.alloy.B.a.clock.J m)
  (reserve:q+226≤prec)

private theorem reserve_three {q p:ℕ} (h:q+226≤p) :
    2*18*3+(q+(2*18+1)*3+1+3)+3≤p := by omega

private theorem order_three {q p o:ℕ} (h:q+226≤p) (depth₁:2*(p+1)+8≤o) :
    3+(q+(2*18+1)*3+1)≤o+1 := by omega

include history scroll chamber hospital protection deep aged hp cp ep path pass month volume narrow enrolled reserve closeDates in
theorem on_post (calendarPaid:window) (S:initial) (birth:∀ v,(S.w v)⁻¹≤U₀*(x₀⁻¹)^36) (rent:S.rent≤x₀^prec) : sale S ∧ faces S q span H angleCap ε :=
  let x:Wallet disks:=WilsonThermometerCourseHearing.fired
  let intake:=WilsonReceivedCloseRefundedWindow.original (V:=Fin 3) (X:=fun _=>ℂ) (m:=m) (b:=i+1)
    (N:=i+2) (per:=per) (k:=k) R hk D Q π Γ Ψ books ahead disks (S₀) levels school.order
    school.horizon school.pieces hi (head) S simple
  let booked:=intake history path (Nat.lt_succ_self (i+1)) pass scroll chamber month hospital volume protection
    school.price narrow school.sense school.tall enrolled x
  let selected:=booked 3 18 q prec span degree (U₀) H angleCap cap ε (WilsonReceivedCloseReportedWallet.covers R)
    deep aged hp cp ep closeDates (reserve_three reserve) (order_three reserve deep)
  selected calendarPaid birth rent

include history scroll chamber warm top cal hospital fund slow protection deep aged hp cp ep path pass month volume
  narrow enrolled reserve closeDates in
theorem original (calendarPaid:window) (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (stage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ j,R.family.ref (levels j) ≤ (i+2))
    (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (employment:∀ d,MintClock.Employment D φ d (R.rolls.L d))
    (calendar:MintClock.Regency D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (support:WilsonOriginalThermometerTollBudget.reach R ≤ R.alloy.B.a.clock.J (i+2)+1)
    :
    ∃ S:initial, S.w=w₁ ∧ S.rent=x₀^prec ∧ S.passport=E₀ ∧ S.inputIndex=Empty ∧
      S.op=op ∧ S.lesson=lesson ∧ WilsonReceivedCloseReportedStation.Filed R simple A hk D Q π Γ Ψ
        books hi school o ahead S ∧ sale S ∧ faces S q span H angleCap ε := by
  have takeDates:=calendarPaid
  obtain ⟨_,_,_,_,_,band,cool,_⟩:=takeDates
  obtain ⟨S,w,rent,po,pl,passport,empty,filed,birth⟩:=WilsonReceivedCloseReportedStation.original
    R simple A hk D Q π Γ Ψ history scroll books chamber hi warm top school o op lesson cal ahead hospital
    (f:=f) (F:=F) fund slow late date checked near shape size space room stage ranks width refs income
    employment calendar support narrow band cool prec
  obtain ⟨sold,served⟩:=on_post R simple A hk D Q π Γ Ψ history scroll books chamber hi school o ahead hospital
    protection q prec span degree H angleCap cap ε deep aged hp cp ep path pass month volume closeDates
    narrow enrolled reserve calendarPaid S birth rent.le
  exact ⟨S,w,rent,passport,empty,po,pl,filed,sold,served⟩

end YM.Integration.WilsonReceivedCloseReportedPanel
