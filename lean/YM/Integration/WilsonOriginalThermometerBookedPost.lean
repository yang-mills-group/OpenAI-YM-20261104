import YM.Integration.WilsonOriginalThermometerElectedPost

/-! The full elected thermometer post with its source price fixed before the period. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalThermometerBookedPost
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
  (history:Concourse R.alloy R.kit R.T π Γ m (i+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+1)) (R.family.path.levels.clock.forcedAllowance (i+1)))
  (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (i+1) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=i+1) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+1) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M₀" => primitive R A (i+1) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+1)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self i) o

variable {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
  {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)

/-- All scale conditions used to buy the three original cutoff coordinates precede the period and sites. -/
def opening : ℕ :=
  (eventually_atTop.mp (WilsonOriginalThermometerTopGrading.original R (f:=f) (H:=F)
    simple fund slow 1 zero_lt_one)).choose

local notation "E₁" => max 1 ((1+WilsonOriginalThermometerTopGrading.cap R i 1)*wallet R levels σ₀)
local notation "w₁" => (fun _:Fin 3 => ((E₁)*(Ω₀))⁻¹)

include history scroll chamber warm top cal hospital fund slow in
theorem original (late:opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (stage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J i)
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+1))
    (refs:∀ j,R.family.ref (levels j) ≤ (i+1)) {τ:ℝ} (pos:0<τ) (bounded:τ≤1) :
    ∃ P:WilsonOriginalReceivedChain.Post (N:=i+1) R hk D Q π Γ Ψ books ahead disks S₀ levels
      school.order school.horizon school.pieces i hi (head),
      P.w=w₁ ∧ P.rent=τ ∧ P.cost=(Ω₀)⁻¹ ∧ P.passport=E₀ ∧ Countable P.inputIndex ∧
      P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
      ∀ s:(J₀).Mode, Poly.toll P.w s*((E₁)*(Ω₀))^s.val.card=1 := by
  have rich:1 ≤ Ω₀ := (by norm_num : (1:ℝ)≤4).trans (MintClock.Page.roofers ..)
  have heard:=(eventually_atTop.mp (WilsonOriginalThermometerTopGrading.original R (f:=f) (H:=F)
    simple fund slow 1 zero_lt_one)).choose_spec i late A date checked near σ₀ (Ω₀) rich per o.origin
    school.order op.count school.horizon op.stage k (R.alloy.B.a.clock.J i) (shape.ge.trans' size)
    space room stage (school.price.trans ((Nat.le_succ _).trans (hk.trans (R.alloy.B.a.fits.mono hi))))
    ranks school.tall
  obtain ⟨salary,vote,tests,toll⟩:=heard
  obtain ⟨P,weights,rent,cost,passport,counted,idx,opEq,lessonEq⟩:=
    WilsonOriginalThermometerElectedPost.counted R simple A hk D Q π Γ Ψ history scroll books chamber hi warm top
      school (w₁) o op lesson cal ahead hospital pos bounded (inv_le_one_of_one_le₀ rich) le_rfl
      shape salary vote tests width refs
  exact ⟨P,weights,rent,cost,passport,counted,idx,opEq,lessonEq,fun s=>weights ▸ toll s⟩

end YM.Integration.WilsonOriginalThermometerBookedPost
