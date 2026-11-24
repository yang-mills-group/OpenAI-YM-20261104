import YM.Integration.WilsonThermometerRegisteredStation
import YM.Integration.WilsonReceivedCloseReportedWallet
import YM.Integration.WilsonMovingMentorPagePrice

/-! The measured twice-inverse station with its copied independent program on the same saved post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseReportedStation
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


local notation "entrance" => WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels
      school.order school.horizon school.pieces (i+1) hi (head)

def Filed (P:entrance) : Prop :=
  P.modelIndex=Entry R levels ∧ HEq P.model (M₀) ∧
      ∀ (x : Wallet disks) (grid : Side) (mult : (R.family.side (i+1) per).val ∣ grid.val)
        (d : ℕ), d ≤ school.order → ∀ a : Stationary.Link G grid,
        WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x grid mult d a =
          peek mult (Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead disks
            P.model school.order P.voter) levels (π (i+2)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) x d a

include history scroll chamber warm top cal hospital fund slow in
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
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
    (narrow:school.horizon ≤ R.alloy.B.a.clock.J m)
    (priceDate:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ i+1)
    (cooled:(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ i+1) (p:ℕ) :
    let x:=regulatorRun R.family (i+2) per (i+1)
    ∃ P:entrance, P.w=w₁ ∧ P.rent=x^p ∧ P.op=op ∧ P.lesson=lesson ∧ P.passport=E₀ ∧ P.inputIndex=Empty ∧
      Filed R simple A hk D Q π Γ Ψ books hi school o ahead P ∧
      ∀ v,(P.w v)⁻¹ ≤ WilsonReceivedCloseReportedWallet.unit R*(x⁻¹)^36 := by
  intro x
  have cold:=(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec (i+1) cooled
    (i+2) per (Nat.le_succ _)
  have xp:0<x:=cold.1
  have small:x≤1:=by change regulatorRun R.family (i+2) per (i+1)≤1; linarith only [cold.1,cold.2]
  obtain ⟨P,w,rent,_,passport,_,empty,po,pl,_,idx,model,bank⟩:=WilsonThermometerRegisteredStation.original
    R simple A hk D Q π Γ Ψ history scroll books chamber hi warm top school o op lesson cal ahead hospital
    (f:=f) (F:=F) fund slow late date checked near shape size space room stage ranks width refs
    (pow_pos xp p) (pow_le_one₀ xp.le small)
  have paged:=WilsonMovingMentorPagePrice.at_date R books ahead employment calendar (i+1) op
    (Oak.era R hk D Q π Γ hi op lesson) school.order school.horizon (narrow.trans (R.alloy.B.a.fits.mono hi))
    stage (shape.trans_le school.sense)
  have fee:=WilsonReceivedCloseReportedWallet.sold R simple D φ income i (Burn.horizon k)
    (i+2) per (Nat.le_succ _) ((Nat.le_add_right (Burn.horizon k) 2).trans
      (hk.trans (R.alloy.B.a.fits.mono (hi.trans (Nat.le_succ (i+1)))))) support priceDate
    (Ω:=Ω₀) ((by norm_num : (0:ℝ) ≤ 4).trans paged.2.1) paged.2.2.1
  refine ⟨P,w,rent,po,pl,passport,empty,⟨idx,model,bank⟩,?_⟩
  intro v
  rw [w]
  simpa only [inv_inv] using fee

end YM.Integration.WilsonReceivedCloseReportedStation
