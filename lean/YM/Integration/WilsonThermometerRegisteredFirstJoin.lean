import YM.Integration.WilsonThermometerRegisteredStation
import YM.Integration.WilsonThermometerFirstJoinAppointment

/-! The booked physical and filed independent upper source on the original
reporting date, followed by the measured semester with those very inputs. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredFirstJoin
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

include hk in
private theorem wide {u : ℕ} (stage : m ≤ u) : school.horizon ≤ R.alloy.B.a.clock.J u := by
  have top := hk.trans (R.alloy.B.a.fits.mono stage)
  have short := school.tall
  omega

def Following (floor : m ≤ i) (P : originalPost) (q : ℕ) (ε : ℝ) : Prop :=
  ∃ counted : Countable P.inputIndex, letI := counted
    ∃ h C E : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      Nonempty (WilsonThermometerFirstJoinAppointment.Record R hk D Q π Γ Ψ books ahead
        school.order school.horizon school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history scroll
        chamber hospital (P.capacity.le.trans school.sense) (wide R hk school hi)
        WilsonThermometerCourseHearing.fired q ε h C E t)

include warm top cal in
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (stage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ j,R.family.ref (levels j) ≤ (i+2)) {τ:ℝ} (pos:0<τ) (bounded:τ≤1)
    (floor : m ≤ i) (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (q : ℕ) (deep : 2*q+8 ≤ school.order) (aged : q+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (funded : WilsonReceivedMeasuredStampPrice.opening R simple q school.order k deep aged ep ≤ i+1) :
    ∃ P:WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels
      school.order school.horizon school.pieces (i+1) hi (head),
      P.w=w₁ ∧ P.rent=τ ∧ P.cost=(Ω₀)⁻¹ ∧ P.passport=E₀ ∧ Countable P.inputIndex ∧
      P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
      (∀ s:(J₀).Mode, Poly.toll P.w s*((E₁)*(Ω₀))^s.val.card=1) ∧
      P.modelIndex=Entry R levels ∧ HEq P.model (M₀) ∧
      (∀ (x : Wallet disks) (grid : Side) (mult : (R.family.side (i+1) per).val ∣ grid.val)
        (d : ℕ), d ≤ school.order → ∀ a : Stationary.Link G grid,
        WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x grid mult d a =
          peek mult (Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead disks
            P.model school.order P.voter) levels (π (i+2)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) x d a) ∧
      Following R simple A hk D Q π Γ Ψ history scroll books chamber hi school o ahead hospital floor P q ε := by
  obtain ⟨P,weights,rent,cost,passport,counted,idx,opEq,lessonEq,toll,names,rows,copies⟩ :=
    WilsonThermometerRegisteredStation.original R simple A hk D Q π Γ Ψ history scroll books chamber hi
      warm top school o op lesson cal ahead hospital fund slow late date checked near shape size space room
      stage ranks width refs pos bounded
  refine ⟨P,weights,rent,cost,passport,counted,idx,opEq,lessonEq,toll,names,rows,copies,counted,?_⟩
  letI : Countable P.inputIndex := counted
  exact WilsonThermometerFirstJoinAppointment.original R hk D Q π Γ Ψ books ahead school.order school.horizon
    school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history scroll chamber hospital
    (P.capacity.le.trans school.sense) (wide R hk school hi) WilsonThermometerCourseHearing.fired path pass month
    school.price (wide R hk school floor) school.sense school.tall q deep aged ep funded

end YM.Integration.WilsonThermometerRegisteredFirstJoin
end
