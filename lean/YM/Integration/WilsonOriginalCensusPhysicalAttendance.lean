import YM.Integration.WilsonOriginalCensusDatedSchools

/-! The two material postings use one original physical school. The timetable is
chosen before the period. Its history supplies the actual Wilson density and
the strong original hard allowance at every occupied date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPhysicalAttendance
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonReportingAbsoluteInletSchool WilsonWindowUniversalSchool
open FormalBulk08 FormalBulk08.Flat Push.PriceCompiler
open WilsonOriginalCollarElection WilsonOriginalCollarTeacher QuadraticLocal.Advent.Oak QuadraticLocal.Affinity
open LocalComparison
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
  {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {T:Campaign R} {W:Campaign.Pillars R T}

abbrev roots (s:WilsonOriginalAllOrderCourse.Schedule G)(R:Run G)(simple:G.Simple) :=
  WilsonOlderFreshGraphSchool.roots (menu (WilsonOriginalAllOrderCourse.teacher s)) simple R.metals.p R.metals.K

abbrev tab (s:WilsonOriginalAllOrderCourse.Schedule G)(R:Run G)(simple:G.Simple) :=
  WilsonOlderFreshGraphSchool.rollTab (menu (WilsonOriginalAllOrderCourse.teacher s)) simple R.metals R.rolls

local notation "D" => roots s R simple
local notation "Q" => tab s R simple
local notation "scroll" => WilsonPhysicalHistoryPriorAperture.law G MintClock.splits

structure Room (s:WilsonOriginalAllOrderCourse.Schedule G)(R:Run G)(simple:G.Simple) where
  books : Offices.Books (roots s R simple) R.rolls (tab s R simple) MintClock.splits
  ahead : Forecast (roots s R simple) R.rolls (tab s R simple) MintClock.splits books
  chamber : VowsR.Chamber (WilsonPhysicalHistoryPriorAperture.law G MintClock.splits) R.kit
    (roots s R simple) (tab s R simple) books
  hospital : MintClock.Hospital (roots s R simple) R.rolls (tab s R simple) R.kit.target
    MintClock.splits books ahead R.alloy.delay
  way : WayStation R.kit
  pass : Pass (roots s R simple) (tab s R simple) R.alloy R.kit
  warm : Spill.Raffle.Warm G (roots s R simple) R.alloy.delay MintClock.splits
  month : Scholar.Month R.rolls (roots s R simple) (tab s R simple) R.alloy.delay
  ticket : TicketP R.alloy R.kit (roots s R simple) (tab s R simple)
  prior : WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots s R simple) MintClock.splits R.alloy.delay

/-- The two calendars, counts and stages refer to actual consecutive
opportunities, on the single enrolled positive Wilson law at this period. -/
def Receives (s:WilsonOriginalAllOrderCourse.Schedule G)(R:Run G)(simple:G.Simple)
    {vac m N per:ℕ}(school:Syl.School vac)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)
    (hk:Burn.horizon vac+2 ≤ R.alloy.B.a.clock.J m)
    (lessons:∀ i, ∀ (hi : m ≤ i), i < N → Lesson (N:=N) R hk (roots s R simple) (tab s R simple) π Γ hi)
    (Ψ:(i:ℕ) → Rep G (R.family.side i per)) : Prop :=
  Concourse R.alloy R.kit R.T π Γ m N per vac Ψ ∧
  Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
  (∀i,m ≤ i → i ≤ N → (Ψ i).beta=(R.family.path.rep N per i).beta ∧
    (Ψ i).eval=(R.family.path.rep N per i).eval ∧
    ∀q l load,q+l*load ≤ R.alloy.B.a.clock.J i → ∃f,Topline (Ψ i) f ∧
      ((R.alloy.B.a.clock.hatBeta i)^l)^load*f ≤ 
        (R.alloy.B.a.clock.hatBeta i)^(-(q:ℝ))*forcedDivisor R.family i) ∧
  ∀ j, ∀ (hj : m ≤ j), ∀ (neck : j+1 < N),
    Nonempty (Oak.Calendar R hk (roots s R simple) (tab s R simple) π Γ Ψ hj
      (N:=N) (lessons j hj (by omega))) ∧
    Nonempty (Oak.Calendar R hk (roots s R simple) (tab s R simple) π Γ Ψ (Nat.le_succ_of_le hj)
      (N:=N) (lessons (j+1) (Nat.le_succ_of_le hj) neck)) ∧
    ∃(low:Opportunity (R.alloy.B.a.clock.J (j+1)) (R.alloy.B.a.clock.J j))
      (high:Opportunity (R.alloy.B.a.clock.J (j+1+1)) (R.alloy.B.a.clock.J (j+1))),
      low.count=school.pieces ∧ low.stage=school.order+1 ∧ high.count=school.pieces ∧ high.stage=school.order+1

def Sits (s:WilsonOriginalAllOrderCourse.Schedule G)(R:Run G)(simple:G.Simple)
    {vac:ℕ}(school:Syl.School vac)(m:ℕ) : Prop :=
  ∀N,m ≤ N → ∃(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(hk:Burn.horizon vac+2 ≤ R.alloy.B.a.clock.J m)
    (lessons:∀ i, ∀ (hi : m ≤ i), i < N → Lesson (N:=N) R hk (roots s R simple) (tab s R simple) π Γ hi),
    PlanV.Path (roots s R simple) R.alloy (tab s R simple) (Burn.horizon vac) N m π Γ ∧
    ∀per,∃Ψ:(i:ℕ) → Rep G (R.family.side i per),Receives s R simple school π Γ hk lessons Ψ

theorem receive {vac m:ℕ}{school:Syl.School vac}
    (paid:WilsonOriginalCollarCensusSeats.Dated (WilsonOriginalAllOrderCourse.teacher s) simple R school m):
    Sits s R simple school m := by
  intro N band
  obtain ⟨π,Γ,hk,lessons,path,boards⟩:=paid N band
  refine ⟨π,Γ,hk,lessons,path,fun per=>?_⟩
  obtain ⟨Ψ,course,top,opps,hard⟩:=boards per
  refine ⟨Ψ,course,top,?_,?_⟩
  · intro i lo hi
    have reg:=course.1.walk i lo hi
    exact ⟨reg.beta,reg.view,hard i lo hi⟩
  · intro j hj neck
    obtain ⟨cl,opL,cntL,stL⟩:=opps j hj (by omega)
    obtain ⟨ch,opH,cntH,stH⟩:=opps (j+1) (Nat.le_succ_of_le hj) neck
    exact ⟨cl,ch,opL,opH,cntL,stL,cntH,stH⟩

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W):
    Nonempty (Room s R simple) ∧
      ∀vac (school:Syl.School vac),2 ≤ school.order → ∀ᶠ m in atTop,Sits s R simple school m :=by
  obtain ⟨B,F,_,_,ch,hos,warm,month,tick,prior,_⟩:=paid.house
  exact ⟨⟨⟨B,F,ch,hos,paid.books.1,tick.pledge,warm,month,tick,prior⟩⟩,
    fun v S deep=>(paid.seats v S deep).mono fun _ due=>receive due⟩

end YM.Integration.WilsonOriginalCensusPhysicalAttendance
end
