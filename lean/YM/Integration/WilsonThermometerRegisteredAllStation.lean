import YM.Integration.WilsonThermometerRegisteredAllFiled
import YM.Integration.WilsonThermometerCommonDetector

/-! The independent ordinary program on the same appointed, once-compensated real lower post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredAllStation
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

local notation "originalPost" => WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks
  (WilsonThermometerCourseHearing.sectors) levels school.order school.horizon school.pieces (i+1) hi
  (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self (i+1)) o)

open private wide from YM.Integration.WilsonThermometerRegisteredFirstJoin
open WilsonOriginalThermometerTollBudget
open RG QuadraticLocal.Affinity

open WilsonReceivedCloseHistory
open WilsonOriginalReceivedChain


open WilsonThermometerCommonDetector
local notation "S₁" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o
local notation "gf" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "lowerPost" f:max => WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels
  school.order school.horizon school.pieces i f (S₁)
local notation "young" f:max L:max => Oak.student (n:=per) R hk D Q π Γ books f (L).op (L).lesson ahead disks
  (L).model school.order (L).voter
local notation "issued" x:max f:max L:max => Air.craft (young f L) (fun v=>((young f L) v).paint x)
  levels (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))

def Visible (floor:m ≤ i) (L:lowerPost floor) (q:ℕ) (ε:ℝ) : Prop :=
  (8*(Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead school.order school.horizon)^school.pieces)*L.rent ≤
    ε*gf^q ∧ (∀ s:(J₀).Mode,gf^157 ≤ Poly.toll L.w s) ∧ L.op.count ≤ Burn.horizon k+2 ∧
    school.horizon ≤ R.alloy.B.a.clock.J i ∧
    ∀ (x:Wallet disks) (z:Stationary.Link G (R.family.side i per)),
      WilsonThermometerRegisteredAllFiled.numerical R A π Γ school o x z =
        Poly.pass (WilsonCoherentMayerWindingGrades.panel school.order (gf:ℂ)
          (fun d=>Air.discharge (issued x floor L) d (Stationary.arm G (R.family.side i per) 1 z)))

theorem on_trail (floor:m ≤ i) (pass:AllOrder.Transit.Pass D Q R.alloy R.kit)
    (month:Scholar.Month R.rolls D Q R.alloy.delay) (fits:school.order ≤ Burn.horizon k+1)
    (shelf:school.horizon ≤ R.alloy.B.a.clock.J m) (P:originalPost)
    (q p:ℕ) (ε:ℝ) (hard:WilsonWindowOriginalHardRadius.Booked R.kit)
    (copies:∀ (x:Wallet disks) (grid:Side) (mult:(R.family.side (i+1) per).val∣grid.val)
      (d:ℕ), d ≤ school.order → ∀ a:Stationary.Link G grid,
      WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x grid mult d a =
        peek mult (Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead disks
          P.model school.order P.voter) levels (π (i+2)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) x d a)
    (together:Coissued R simple A hk D Q π Γ Ψ history scroll books chamber hi school o ahead hospital
      floor P q p ε hard) : ∃ L:lowerPost floor, Visible R simple A hk D Q π Γ Ψ books school o ahead floor L q ε := by
  obtain ⟨counted,certified⟩:=together
  letI : Countable P.inputIndex:=counted
  let U:=WilsonOriginalReceivedFirstEnrollment.installed R hk D Q π Γ Ψ books ahead disks S₀ levels
    school.order school.horizon school.pieces (i+1) hi (head) P simple (Nat.lt_succ_self (i+1))
    history scroll chamber hospital (P.capacity.le.trans school.sense) (wide R hk school hi)
    WilsonThermometerCourseHearing.fired
  obtain ⟨h,C,E,rec,L,_,_,_,trail,tiny,roof,load,narrow,_⟩:=certified
  refine ⟨L,tiny,roof,load,narrow,?_⟩
  intro x z
  exact WilsonThermometerRegisteredAllFiled.on_trail R A π Γ school o simple hk D Q Ψ books ahead
    floor U L history pass month fits shelf copies trail x z

include history scroll chamber hospital warm top cal in
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (stage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ j,R.family.ref (levels j) ≤ (i+2))
    (floor : m ≤ i) (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (q : ℕ) (deep : 2*(q+1)+8 ≤ school.order) (aged : (q+1)+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (funded : WilsonReceivedMeasuredStampPrice.opening R simple (q+1) school.order k deep aged zero_lt_one ≤ i+1)
    (hard : WilsonWindowOriginalHardRadius.Booked R.kit) (way : WayStation R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay) (p : ℕ)
    (lower : WilsonThermometerAppointedPhysical.activation R D simple income p ≤ i)
    (ordered : p+156 ≤ school.order+1) (ready : p+6*school.pieces ≤ Burn.horizon k+2)
    (extent : reach R ≤ R.alloy.B.a.clock.J (i+2)+1)
    (topReady : topAge R simple ≤ i)
    (detector : WilsonThermometerAppointedDetector.activation R simple q school.pieces ep ≤ i)
    (measured : (Ψ (i+1)).beta = (R.family.path.rep (i+2) per (i+1)).beta)
    (fits:school.order ≤ Burn.horizon k+1) (shelf:school.horizon ≤ R.alloy.B.a.clock.J m) :
    ∃ L:lowerPost floor, Visible R simple A hk D Q π Γ Ψ books school o ahead floor L q ε := by
  obtain ⟨P,_,_,_,_,_,_,_,_,_,_,_,copies,coissued⟩ :=
    WilsonThermometerCommonDetector.original R simple A hk D Q π Γ Ψ history scroll books chamber hi warm top
      school o op lesson cal ahead hospital fund slow late date checked near shape size space room stage ranks
      width refs floor pass path month q deep aged ep funded hard way training income p lower ordered ready extent
      topReady detector measured
  exact on_trail R simple A hk D Q π Γ Ψ history scroll books chamber hi school o ahead hospital floor
    pass month fits shelf P q p ε hard copies coissued

end YM.Integration.WilsonThermometerRegisteredAllStation
