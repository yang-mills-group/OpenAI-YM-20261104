import YM.Integration.WilsonOriginalCensusAttendancePair

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusAttendanceStation
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonReportingAbsoluteInletSchool WilsonWindowUniversalSchool
open FormalBulk08 FormalBulk08.Flat Push.PriceCompiler
open WilsonOriginalCollarElection WilsonOriginalCollarTeacher QuadraticLocal.Advent.Oak QuadraticLocal.Affinity
open LocalComparison
open scoped Classical BigOperators Topology

open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance
variable {G:Gauge}{s:WilsonOriginalAllOrderCourse.Schedule G}{R:Run G}{simple:G.Simple}
variable {vac m N:ℕ}{school:Syl.School vac}

structure Day (s:WilsonOriginalAllOrderCourse.Schedule G)(R:Run G)(simple:G.Simple)
    {vac:ℕ}(school:Syl.School vac)(m N:ℕ) where
  π : ℕ → Layout G
  Γ : ℕ → Pace.Coin
  hk : Burn.horizon vac+2 ≤ R.alloy.B.a.clock.J m
  lessons : ∀ i, ∀ (h:m ≤ i), i < N → Lesson (N:=N) R hk (roots s R simple)
    (tab s R simple) π Γ h
  path : PlanV.Path (roots s R simple) R.alloy (tab s R simple) (Burn.horizon vac) N m π Γ
  Ψ : ∀ per i, Rep G (R.family.side i per)
  seen : ∀ per, Receives s R simple school π Γ hk lessons (Ψ per)

theorem choose_day (seated:Sits s R simple school m)(band:m ≤ N) :
    Nonempty (Day s R simple school m N) :=by
  obtain ⟨π,Γ,hk,unary,path,boards⟩:=seated N band
  choose Ψ receipt using boards
  exact ⟨⟨π,Γ,hk,unary,path,Ψ,receipt⟩⟩

/-- This internal degree is fixed before the school and its periods. It
serves both finite weak ranks and the native retained-order upper gate. -/
def degree (q p height:ℕ) := max (max q (3*height)) (2*(p+1)+8)

theorem calibrated (q p height:ℕ){n:ℕ}(grades:Fin n → ℕ) :
    let Q:=degree q p height
    let ask:=quote Q p grades
    ask.order=Q ∧ q ≤ Q ∧ 3*height ≤ Q ∧ Q ≤ Burn.horizon ask.vac+1 :=by
  intro Q ask
  have hg:2*(p+1)+8 ≤ Q:=le_max_right ..
  have eq:ask.order=Q:=by
    change max Q (2*(p+1)+8)=Q
    exact max_eq_left hg
  refine ⟨eq,(le_max_left q _).trans (le_max_left ..),(le_max_right q _).trans (le_max_left ..),?_⟩
  change Q ≤ 3*(n+max Q (2*(p+1)+8)+(∑v,grades v)+p+4)+1
  omega

end YM.Integration.WilsonOriginalCensusAttendanceStation
end
