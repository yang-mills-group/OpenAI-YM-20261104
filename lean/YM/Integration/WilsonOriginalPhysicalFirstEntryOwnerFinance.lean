import YM.Integration.WilsonOriginalAllOrderCourse
import YM.Integration.WilsonCloseCaptureFinances
import YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerCourse
import YM.Integration.FundedOriginalVacuumPaths

/-! Pay the two quantitative projection tariffs and the full original vacuum
path books in the same length/delay election as the physical marked fields. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerFinance
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonFundedWindowCompany WilsonFundedWindowMenu WilsonWindowJointPurchase WilsonWindowBookPurchase
open WilsonReportingAbsoluteInletSchool WilsonWindowUniversalSchool
open FormalBulk08 FormalBulk08.Flat Push.PriceCompiler
open OPE.Owl WilsonCoeffUV WilsonCoeffUV.Bank
open LocalComparison
open WilsonOriginalCollarElection WilsonOriginalCollarTeacher QuadraticLocal.Advent.Oak QuadraticLocal.Affinity
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open scoped Classical BigOperators Topology
open WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse
universe u
variable {G : Gauge}

/-- The independent path books and both numerical forecasts are purchased at
the same original menu, before any run, source placement or cutoff is chosen. -/
def receipts : Prediction G := @Together G (@FundedOriginalVacuumPaths.prices G)
  (@Together G (@WilsonThermometerClusterProjectionBudget.Eligible G) (@WilsonReportLampForecast.Eligible G))

theorem buy : AllPrices (@receipts G) := fun s q =>
  joint (from_guard (of_prepaid (FundedOriginalVacuumPaths.buy s q)))
    (joint (WilsonThermometerClusterProjectionBudget.allPrices s q) (WilsonReportLampForecast.allPrices s q))

/-- Coelect the actual whole marked programme, its original quiet and the entrance tariffs. -/
theorem original (a:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(s:WilsonOriginalAllOrderCourse.Schedule G):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
      WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W ∧
      WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels ∧
      WilsonReportLampForecast.Ready R.family.path.levels ∧ FundedOriginalVacuumPaths.prices R.kit := by
  let v := combined (rows s) (events s)
  let basic := @Together G (@FundedMarkedCoverRows.prices G v) (@WilsonReportColumnSubsidy.Eligible G)
  let extra := @Together G (@basic) (@receipts G)
  have fees : AllPrices (@extra) := fun s q =>
    joint (joint (from_guard (of_prepaid (FundedMarkedCoverRows.purchase v s q)))
      (WilsonReportColumnSubsidy.allPrices s q)) (buy s q)
  obtain ⟨R,T,W,opening,seats,gates,patch,house,_,neutral,more,course,semester,stripsPaid,
    nested,panels,support,quiet,pub⟩ :=
    WilsonOriginalCollarWidthReceipt.original.{u} a (bound s.cap) (bound s.chronology)
      (increasing s.cap) simple positive law le_rfl
      (fun s _ => WilsonPhysicalHistoryPriorSelection.permitted MintClock.splits s _)
      (teacher s) (strips s) (bills s) (tube G) (@extra) fees
  refine ⟨R,T,W,?_,more.2.2.1,more.2.2.2,more.2.1⟩
  exact ⟨⟨_,course⟩,opening,seats,gates,patch,house,
    WilsonOriginalAllOrderFiledRealm.original (rows s) (events s) R simple more.1.1,neutral,
    course.2.1.2.1,more.1.2,semester,stripsPaid,nested,panels,support,quiet,
    fun cohort granted => WilsonOriginalAllOrderPublicFields.original (pub cohort granted)⟩

/-- These four grants are already attached to the given all-order marked course. -/
theorem attached {a:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
    {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W):
    RG05Preconstruction.ReadoutPurchase R.b ∧ WilsonWindowReportingPace.Slow R.kit ∧
      PhysicalNext.Repeat.Legato.Cater R.family R.doors ∧ WilsonPositionProgramNestedLengths.Nested R.rolls := by
  obtain ⟨_,_,_,_,_,_,_,pace,_,_,_,fund,_⟩:=paid.originalSchool
  exact ⟨fund.2.2.2.2.2.2.1,pace,(WilsonCloseCaptureFinances.original R simple W fund).2,paid.nested.2.1⟩

/-- All late N/p enrollments and signed P owner hearings on the very same witness. -/
theorem heard {a:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
    {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels)
    (lamp:WilsonReportLampForecast.Ready R.family.path.levels)(D:ℕ) :
    type_of% (WilsonOriginalPhysicalFirstEntryOwnerCourse.original R D simple (attached paid).1
    (attached paid).2.1 (attached paid).2.2.1 bank lamp (attached paid).2.2.2) :=
  WilsonOriginalPhysicalFirstEntryOwnerCourse.original R D simple (attached paid).1
    (attached paid).2.1 (attached paid).2.2.1 bank lamp (attached paid).2.2.2

end YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerFinance
end
