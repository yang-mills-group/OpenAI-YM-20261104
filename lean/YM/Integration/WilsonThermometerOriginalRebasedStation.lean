import YM.Integration.WilsonThermometerOriginalDepositedSlope
import YM.Integration.WilsonThermometerRegisteredStation

/-! Both lowest faces of the real three-source student after its own nonbare scalar reset. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerOriginalRebasedStation
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

open FVA1Physical.TwoReset Exterior Precision

local notation "E₁" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ₀)
local notation "w₁" => (fun _:Fin 3 => ((E₁)*(Ω₀))⁻¹)

include history scroll chamber warm top cal hospital fund slow in
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (stage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ j,R.family.ref (levels j) ≤ (i+2)) {τ:ℝ} (pos:0<τ) (bounded:τ≤1) (live:0<school.order) :
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
      ∀ (v:Wallet disks) (grid:Side) (mult:(R.family.side (i+1) per).val ∣ grid.val)
        (s:Multi.Hot J₀) (y:fieldDir G grid 1),
        let old:=WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o v grid mult
        let K:=(Rebirth.caliber (Γ (i+1)) (Oak.grade0 R hk D Q π Γ hi P.lesson)).back (Burn.horizon k+2)
        let student:=Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead disks
          P.model school.order P.voter
        let atGrade (d:ℕ):=(peek mult student levels (π (i+2)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) v d
          ((Stationary.arm G grid 1).symm y)).part s.val
        WilsonOriginalCoverJetColors.reset school.order old K s 0 y=atGrade 0 ∧
          WilsonOriginalCoverJetColors.reset school.order old K s 1 y=atGrade 1 := by
  obtain ⟨P,hw,hrent,hcost,hpass,numbered,idx,hop,hlesson,tolls,hmodel,hraw,copies⟩:=
    WilsonThermometerRegisteredStation.original R simple A hk D Q π Γ Ψ history scroll books chamber hi warm
      top school o op lesson cal ahead hospital fund slow late date checked near shape size space room stage ranks
      width refs pos bounded
  refine ⟨P,hw,hrent,hcost,hpass,numbered,idx,hop,hlesson,tolls,hmodel,hraw,copies,?_⟩
  intro v grid mult s y
  obtain ⟨a,earned⟩:=WilsonThermometerOriginalDepositedSlope.income R hk D Q π Γ hi P.lesson
  let student:=Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead disks P.model school.order P.voter
  let old:=WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o v grid mult
  obtain ⟨h₀,h₁⟩:=WilsonThermometerOriginalDepositedSlope.table mult student levels (π (i+2))
    (AllOrder.Floe.Step.tape (Burn.horizon k+2)) v school.order (Burn.horizon k+2) live (Γ (i+1)) a earned
    old (copies v grid mult) s y
  exact ⟨h₀.trans (congrArg (fun q=>(q:Poly J₀).part s.val) (copies v grid mult 0 (Nat.zero_le _) _)),
    h₁.trans (congrArg (fun q=>(q:Poly J₀).part s.val) (copies v grid mult 1 live _))⟩

end YM.Integration.WilsonThermometerOriginalRebasedStation
