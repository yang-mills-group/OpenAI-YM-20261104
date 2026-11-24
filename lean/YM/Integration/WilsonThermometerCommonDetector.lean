import YM.Integration.WilsonThermometerFundedPacket
import YM.Integration.WilsonThermometerAppointedDetector
import YM.Integration.WilsonThermometerAppointedTrail
import YM.Integration.WilsonReceivedTaylorWindow

/-! Both original physical appointments, the independent lower pupil,
the earned cold detector and the signed hard split on a single selection. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerCommonDetector
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

def topAge {G : Gauge} (R : Run G) (simple : G.Simple) : ℕ :=
  (eventually_atTop.mp ((tendsto_add_atTop_nat 1).eventually (WilsonReceivedTaylorWindow.potential R simple 0 0))).choose

private theorem carry {I : Sort*} {A : I → Type*} (test : ∀ i, A i → Prop)
    {i j : I} {a : A i} {b : A j} (tag : i=j) (same : HEq b a) (haveIt : test i a) : test j b := by
  subst j
  exact eq_of_heq same ▸ haveIt

def Coissued (floor : m ≤ i) (P : originalPost) (q p : ℕ) (ε : ℝ)
    (hard : WilsonWindowOriginalHardRadius.Booked R.kit) : Prop :=
  ∃ counted : Countable P.inputIndex, letI := counted
    let U := WilsonOriginalReceivedFirstEnrollment.installed R hk D Q π Γ Ψ books ahead disks S₀ levels
      school.order school.horizon school.pieces (i+1) hi (head) P simple (Nat.lt_succ_self (i+1))
      history scroll chamber hospital (P.capacity.le.trans school.sense) (wide R hk school hi)
      WilsonThermometerCourseHearing.fired
    ∃ (h C E : ℝ) (receipt : WilsonThermometerFirstJoinAppointment.Record R hk D Q π Γ Ψ books ahead
      school.order school.horizon school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history scroll
      chamber hospital (P.capacity.le.trans school.sense) (wide R hk school hi) WilsonThermometerCourseHearing.fired
      (q+1) 1 h C E ((Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta)^(q+1)))
      (L : Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels school.order school.horizon school.pieces
        i floor (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_of_succ_lt (Nat.lt_succ_self (i+1))) o)),
      HEq L receipt.post ∧ HEq L.input receipt.post.input ∧ HEq L.output receipt.post.output ∧
      Trail R hk D Q π Γ Ψ books ahead disks S₀ levels school.order school.horizon school.pieces hi
        (head) U i floor (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_of_succ_lt (Nat.lt_succ_self (i+1))) o) L ∧
      (8*(Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead school.order school.horizon)^school.pieces)*L.rent ≤
         ε*(Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta)^q ∧
      (∀s:(J₀).Mode,(Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta)^157 ≤ Poly.toll L.w s) ∧
      L.op.count ≤ Burn.horizon k+2 ∧ school.horizon ≤ R.alloy.B.a.clock.J i ∧
      (∀ (d : ℕ) (select : (J₀).Mode → Prop) (v : Fin 3) (contains : ∀s, select s → v∈s.val)
          (distant : ∀s, select s → ∃a∈s.val, ∃b∈s.val,
            d*(4*(P₀).p.B+2)+2*(P₀).p.B ≤ separation (P.passport.origin a) (P.passport.origin b)),
          WilsonThermometerGrantedPacket.Paid R hk D Q π Γ Ψ books ahead school.order school.horizon
            school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history scroll chamber hospital
            (P.capacity.le.trans school.sense) (wide R hk school hi) WilsonThermometerCourseHearing.fired
            receipt hard d select v contains distant p)

include warm top cal in
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
    (measured : (Ψ (i+1)).beta = (R.family.path.rep (i+2) per (i+1)).beta) :
    ∃ P:WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels
      school.order school.horizon school.pieces (i+1) hi (head),
      P.w=w₁ ∧ P.rent=(Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta)^(q+1) ∧ P.cost=(Ω₀)⁻¹ ∧ P.passport=E₀ ∧ Countable P.inputIndex ∧
      P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
      (∀ s:(J₀).Mode, Poly.toll P.w s*((E₁)*(Ω₀))^s.val.card=1) ∧
      P.modelIndex=Entry R levels ∧ HEq P.model (M₀) ∧
      (∀ (x : Wallet disks) (grid : Side) (mult : (R.family.side (i+1) per).val ∣ grid.val)
        (d : ℕ), d ≤ school.order → ∀ a : Stationary.Link G grid,
        WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x grid mult d a =
          peek mult (Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead disks
            P.model school.order P.voter) levels (π (i+2)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) x d a) ∧
      Coissued R simple A hk D Q π Γ Ψ history scroll books chamber hi school o ahead hospital floor P q p ε hard := by
  let gt := Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta
  have gt₀ : 0<gt := ActualRunKernelPackets.regulator_pos R (i+2) per (i+2) le_rfl
  have window := (eventually_atTop.mp ((tendsto_add_atTop_nat 1).eventually
    (WilsonReceivedTaylorWindow.potential R simple 0 0))).choose_spec i topReady
  have gt₁ : gt≤1 := (window (i+2) per (Nat.lt_succ_self (i+1)) 0 (by simp)).1
  have lowerRent : 0<gt^(q+1) := pow_pos gt₀ _
  have safe : gt^(q+1)≤1 := pow_le_one₀ gt₀.le gt₁
  obtain ⟨P,weights,rent,cost,passport,counted,idx,opEq,lessonEq,toll,names,rows,copies,following⟩ :=
    WilsonThermometerFundedPacket.original R simple A hk D Q π Γ Ψ history scroll books chamber hi warm top
      school o op lesson cal ahead hospital fund slow late date checked near shape size space room stage ranks width refs
      lowerRent safe floor pass path month (q+1) deep aged zero_lt_one funded hard way training income p
      lower ordered ready extent le_rfl measured
  refine ⟨P,weights,rent,cost,passport,counted,idx,opEq,lessonEq,toll,names,rows,copies,?_⟩
  obtain ⟨count,rest⟩ := following
  letI : Countable P.inputIndex := count
  obtain ⟨h,C,E,booked⟩ := rest
  obtain ⟨receipt,charge⟩ := booked (gt^(q+1)) lowerRent safe
  have wages : ∀a : Fin 3, P.w a =
      ((E₁)*(Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead school.order school.horizon))⁻¹ := by
    intro a
    rw [opEq,lessonEq]
    exact congrFun weights a
  obtain ⟨L,same,_,_,_,_,old,forced,tiny,roof⟩ := WilsonThermometerAppointedDetector.original R hk D Q π Γ Ψ
    books ahead school.order school.horizon school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history
    scroll chamber hospital (P.capacity.le.trans school.sense) (wide R hk school hi) WilsonThermometerCourseHearing.fired
    q receipt refs income ep detector extent rent wages
  refine ⟨count,h,C,E,receipt,L,same,old,forced,?_,tiny,roof,L.capacity.le.trans school.sense,
    wide R hk school floor,charge⟩
  have enough : P.rent+1*gt^(q+1) ≤ 2 := by rw [one_mul]; linarith only [P.small,safe]
  have trail := WilsonThermometerAppointedTrail.original R hk D Q π Γ Ψ books ahead school.order school.horizon
    school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history scroll chamber hospital
    (P.capacity.le.trans school.sense) (wide R hk school hi) WilsonThermometerCourseHearing.fired receipt enough
  exact carry _ (WilsonThermometerOfferedStep.original R A simple (Nat.lt_succ_self (i+1)) o refs) same trail

end YM.Integration.WilsonThermometerCommonDetector
end
