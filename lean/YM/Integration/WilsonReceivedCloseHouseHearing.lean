import YM.Integration.WilsonReceivedCloseCopiedThermometer
import YM.Integration.WilsonReceivedCloseThreeSlotSchool
import YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool

/-! A concrete three-field hearing at the grade, registrar and dates paid by one original marked house. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseHouseHearing
open Pert.Asymptotics
open WilsonOriginalReceivedChain WilsonReceivedCloseHistory Extra.Histories MergeProof.Accent
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
section
/-- One genuine original entrance, its complete printed program, and every paid ordinary face. -/
def Receipt (q prec span:ℕ) (H angleCap ε:ℝ) : Prop :=
    ∃ S:initial, S.w=w₁ ∧ S.rent=x₀^prec ∧ S.passport=E₀ ∧ S.inputIndex=Empty ∧
      S.op=op ∧ S.lesson=lesson ∧ WilsonReceivedCloseReportedStation.Filed R simple A hk D Q π Γ Ψ
        books hi school o ahead S ∧ WilsonReceivedCloseCopiedThermometer.Published R simple A hk D Q π Γ Ψ books hi school o ahead S ∧ sale S ∧ faces S q span H angleCap ε
end
end YM.Integration.WilsonReceivedCloseHouseHearing
namespace YM.Integration.WilsonReceivedCloseHouseHearing
open Pert.Asymptotics
open WilsonOriginalReceivedChain WilsonReceivedCloseHistory Extra.Histories MergeProof.Accent
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators


open WilsonReceivedCloseThreeSlotSchool Sycamore
variable {G:Gauge} (R:Run G) (simple:G.Simple)
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
    {φ:ℕ→ℕ} (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
    (ahead:Mentor.Forecast D R.rolls Q φ books) {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
    (house:Treehouse.VariableHouse R D Q scroll books ZΘ ahead profile)
    {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
    {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (protection:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (hire:∀d,MintClock.Employment D φ d (R.rolls.L d))
    (q span degree:ℕ) (H angleCap cap ε:ℝ) (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "κ" => WilsonReceivedCloseThreeSlotSchool.vacuum R q
local notation "Sch₀" => WilsonReceivedCloseThreeSlotSchool.school R q
local notation "Ready₀" m:max i:max => WilsonReceivedCloseThreeSlotSchool.Prepared R simple D φ protection
  (f:=f) (F:=F) fund slow q span degree H angleCap cap ε hp cp ep m i
variable {m i per:ℕ} (hi:m ≤ i+1) (paid:WilsonReceivedCloseThreeSlotSchool.Prepared R simple D φ protection (f:=f) (F:=F) fund slow q
      span degree H angleCap cap ε hp cp ep m i)
variable (hk:Burn.horizon (WilsonReceivedCloseThreeSlotSchool.vacuum R q)+2 ≤ R.alloy.B.a.clock.J m)
    (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
    (lesson:Lesson (N:=i+2) R hk D Q π Γ hi)
    (path:PlanV.Path D R.alloy Q (Burn.horizon (WilsonReceivedCloseThreeSlotSchool.vacuum R q)) (i+2) m π Γ)
    (history:Concourse R.alloy R.kit R.T π Γ m (i+2) per (WilsonReceivedCloseThreeSlotSchool.vacuum R q) Ψ)
    (top:Topline (Ψ (i+2)) (R.family.path.levels.clock.forcedAllowance (i+2)))
    (closeDates:PaceR.Close R degree cap m (i+1))
    (A:Group R.family 6) (o:Positions (Fin 3) (R.family.side (i+2) per))

local notation "op₀" => WilsonReceivedCloseThreeSlotSchool.opportunity R q i (hk.trans (R.alloy.B.a.fits.mono hi))

include paid house hire income path history top closeDates in
theorem at_period (dating:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A) :
    @Receipt G R simple A m per (κ) i hk D Q π Γ Ψ φ books hi (Sch₀) o (op₀) lesson ahead q (q+226) span H angleCap ε := by
  obtain ⟨cal⟩:=Oak.agrees R hk D Q π Γ Ψ history hi (Nat.lt_succ_self (i+1)) lesson
  exact WilsonReceivedCloseCopiedThermometer.original (m:=m) (i:=i) (per:=per) (k:=κ) (φ:=φ) R simple A hk D Q π Γ Ψ history scroll books
    house.licence.employed hi house.stamps top (Sch₀) o (op₀) lesson cal ahead house.licence.forecast
    (f:=f) (F:=F) fund slow protection q (q+226) span degree H angleCap cap ε
    (WilsonReceivedCloseThreeSlotSchool.degree R q) (WilsonReceivedCloseThreeSlotSchool.allotment R q)
    hp cp ep path house.licence.employed.station.1 house.licence.monthly house.licence.edges closeDates
    paid.room paid.stage le_rfl paid.windows paid.late dating checked near rfl (by change 3 ≤ 3; decide) (by change 14 ≤ 14; decide)
    (Nat.le_max_left _ _) le_rfl paid.ranks paid.width paid.reference income hire house.calendar paid.support

end YM.Integration.WilsonReceivedCloseHouseHearing
