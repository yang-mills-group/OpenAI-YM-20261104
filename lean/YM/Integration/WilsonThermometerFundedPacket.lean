import YM.Integration.WilsonThermometerFirstJoinPacket
import YM.Integration.WilsonThermometerRegisteredFirstJoin

/-! One measured three-field birth, its independently computed upper pupil,
and the complete signed exceptional return on its own following post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerGrantedPacket
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity QuadraticLocal.Tint Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology

open WilsonThermometerCourseHearing WilsonPositionThermometerGradedReading LocalComparison ActualPolynomialContraction MergeProof.Accent
open WilsonOriginalStarSceneRent WilsonOriginalThermometerTollBudget
open WilsonOriginalThermometerMicroscopic


variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (order shelf seats : ℕ) (floor : m ≤ j) (A : Group R.family 6)
  (simple : G.Simple) (cut : j+1<N) (o : Positions (Fin 3) (R.family.side N per))
local notation "actors" => disks
local notation "pieces" => sectors
local notation "grades" => (fun z : Fin 3 => (grade z).val)

variable (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) (offered R A simple cut o))

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) ((offered R A simple cut o) x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "hi" => floor.trans (Nat.le_succ j)
variable [Countable P.inputIndex]
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (load:P.op.count≤Burn.horizon k+2) (wide:shelf≤R.alloy.B.a.clock.J (j+1)) (test:Wallet actors)
local notation "initial" op:max => op R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
  (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test
local notation "issued" => initial WilsonOriginalReceivedFirstEnrollment.installed
local notation "coarsePost" => Post (N:=N) (V:=Fin 3) (X:=fun _ => ℂ) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor earlier
variable {firstOrder : ℕ} {ε h C E τ : ℝ}
  (receipt : WilsonThermometerFirstJoinAppointment.Record R hk D Q π Γ Ψ books ahead order shelf seats floor
    A simple cut o P course scroll chamber hospital load wide test firstOrder ε h C E τ)
variable (funded:WilsonWindowOriginalHardRadius.Booked R.kit) (d:ℕ) (select:(Stock.census (Fin 3)).Mode→Prop)
  (v:Fin 3) (contains:∀t,select t→v∈t.val)
local notation "fine" => Ψ ((j+1)+1)
local notation "quote" => Time.quoteHard R.alloy.B.a (j+1) R.kit.book (fine).beta
local notation "delta" => (↑((Real.exp ((fine).p.supportExponent/8*d))⁻¹):ℂ)
local notation "markers" dist₀:max => WilsonOriginalReceivedFirstMarkers.terms R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test funded d select v contains dist₀
local notation "charged" dist₀:max => WilsonOriginalReceivedFirstMarkers.width R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test funded d select v contains dist₀
local notation "apart" => ∀t, select t→∃a∈t.val, ∃b∈t.val,
    d*(4*(fine).p.B+2)+2*(fine).p.B ≤ separation (P.passport.origin a) (P.passport.origin b)
local notation "sector" => Hard (Wallet actors) (Ψ (j+1)).p (Ψ (j+1)).activities.forced (Ψ (j+1)).activities.K
  receipt.post.passport.origin (Stock.census (Fin 3))

local instance : Countable receipt.post.inputIndex := receipt.counted


open WilsonThermometerAppointedPhysical
local notation "wallet₀" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R j 1)*
  wallet R WilsonOriginalThermometerPalette.levels (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1))))
local notation "θ" => (Real.exp ((fine).p.supportExponent/8*d))⁻¹
local notation "g" => Coat.gStep (R.family.path.rep N per (j+1)).beta

def Paid (distant : apart) (p : ℕ) : Prop :=
    receipt.post.output.hard.Paid receipt.post.w (Ψ j).p.B (Ψ j).p.supportExponent
      ((R.alloy.B.a.clock.hatBeta (j+1))^(-(p:ℝ))*LocalComparison.forcedDivisor R.family j) ∧
    ∃ (removed raised : sector), HEq removed (markers distant).removed ∧ HEq raised (markers distant).raised ∧
      WilsonOriginalForcedMarkerMerger.Related v delta removed receipt.post.input.hard raised ∧
      WilsonThermometerRawLog.Priced R hk D Q π Γ Ψ books ahead order shelf seats floor earlier receipt.post removed raised
        θ (θ*WilsonThermometerReportedPower.price R*g^p)

end YM.Integration.WilsonThermometerGrantedPacket
end

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerFundedPacket
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

def Following (floor : m ≤ i) (P : originalPost) (q p : ℕ) (ε : ℝ)
    (hard : WilsonWindowOriginalHardRadius.Booked R.kit) : Prop :=
  ∃ counted : Countable P.inputIndex, letI := counted
    ∃ h C E : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ receipt : WilsonThermometerFirstJoinAppointment.Record R hk D Q π Γ Ψ books ahead
        school.order school.horizon school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history scroll
        chamber hospital (P.capacity.le.trans school.sense) (wide R hk school hi)
        WilsonThermometerCourseHearing.fired q ε h C E t,
        ∀ (d : ℕ) (select : (J₀).Mode → Prop) (v : Fin 3) (contains : ∀ s, select s → v ∈ s.val)
          (distant : ∀s, select s → ∃a∈s.val, ∃b∈s.val,
            d*(4*(P₀).p.B+2)+2*(P₀).p.B ≤ separation (P.passport.origin a) (P.passport.origin b)),
          WilsonThermometerGrantedPacket.Paid R hk D Q π Γ Ψ books ahead school.order school.horizon
            school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history scroll chamber hospital
            (P.capacity.le.trans school.sense) (wide R hk school hi) WilsonThermometerCourseHearing.fired
            receipt hard d select v contains distant p

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
    (funded : WilsonReceivedMeasuredStampPrice.opening R simple q school.order k deep aged ep ≤ i+1)
    (hard : WilsonWindowOriginalHardRadius.Booked R.kit) (way : WayStation R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay) (p : ℕ)
    (lower : WilsonThermometerAppointedPhysical.activation R D simple income p ≤ i)
    (ordered : p+156 ≤ school.order+1) (ready : p+6*school.pieces ≤ Burn.horizon k+2)
    (extent : reach R ≤ R.alloy.B.a.clock.J (i+2)+1) (unit : ε ≤ 1)
    (measured : (Ψ (i+1)).beta = (R.family.path.rep (i+2) per (i+1)).beta) :
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
      Following R simple A hk D Q π Γ Ψ history scroll books chamber hi school o ahead hospital floor P q p ε hard := by
  obtain ⟨P,weights,rent,cost,passport,counted,idx,opEq,lessonEq,toll,names,rows,copies,following⟩ :=
    WilsonThermometerRegisteredFirstJoin.original R simple A hk D Q π Γ Ψ history scroll books chamber hi warm top
      school o op lesson cal ahead hospital fund slow late date checked near shape size space room stage ranks width
      refs pos bounded floor pass path month q deep aged ep funded
  refine ⟨P,weights,rent,cost,passport,counted,idx,opEq,lessonEq,toll,names,rows,copies,?_⟩
  obtain ⟨count,rest⟩ := following
  letI : Countable P.inputIndex := count
  obtain ⟨h,C,E,booked⟩ := rest
  refine ⟨count,h,C,E,?_⟩
  intro t ht t₁
  obtain ⟨receipt⟩ := booked t ht t₁
  refine ⟨receipt,?_⟩
  intro d select v contains distant
  apply WilsonThermometerFirstJoinPacket.original R hk D Q π Γ Ψ books ahead school.order school.horizon
    school.pieces floor A simple (Nat.lt_succ_self (i+1)) o P history scroll chamber hospital
    (P.capacity.le.trans school.sense) (wide R hk school hi) WilsonThermometerCourseHearing.fired
    receipt hard d select v contains distant refs way pass training income p lower ordered extent ep.le unit
  · intro s
    simpa only [opEq,lessonEq] using toll s
  · exact measured
  · exact ready

end YM.Integration.WilsonThermometerFundedPacket
end
