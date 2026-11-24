import YM.Integration.WilsonOriginalOpticalSchedule
import YM.Integration.WilsonCloseCaptureFinances
import YM.Integration.FundedOriginalVacuumPaths
import YM.Integration.WilsonThermometerClusterProjectionBudget
import YM.Integration.WilsonReportLampForecast
import YM.SignedWilsonExpansion.Chron.Binder

/-! Pay the supplementary pre and post bills on the original run. No comparison
 hypothesis in the appointment. Adapt WilsonOriginalPhysicalFirstEntryOwnerFinance.original. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.Election
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12 ThroughLaunch
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
open WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
variable {G : Gauge}
universe u

def receipts : Prediction G := @Together G (@FundedOriginalVacuumPaths.prices G)
  (@Together G (@WilsonThermometerClusterProjectionBudget.Eligible G) (@WilsonReportLampForecast.Eligible G))

theorem buy : WilsonFundedWindowMenu.AllPrices (@receipts G) := fun s q =>
  joint (from_guard (of_prepaid (FundedOriginalVacuumPaths.buy s q)))
    (joint (WilsonThermometerClusterProjectionBudget.allPrices s q) (WilsonReportLampForecast.allPrices s q))

abbrev OrderS (G:Gauge):=WilsonOriginalAllOrderCourse.Schedule G
def leastS (G:Gauge):OrderS G where
  cap :=fun _=> 0
  chronology:=fun _=> 0
  gearBill:=fun _ _ _=>1
  neutral:=fun _=> ⟨(fun _ _ _=>1),(fun _ _ _=>zero_lt_one),(fun _=>1),(fun _=>zero_lt_one),(fun _ _ _=>0)⟩
  extraStrip:=fun _=>⟨(fun _ _ _=>1),(fun _ _ _=>zero_lt_one),(fun _ _=>0),(fun _ _ _=>1)⟩
  fixedDigit:=fun _ _=>⟨1,(fun _=>1),(fun _=>0),0,0,0,le_rfl,univ,0,mem_univ _,fun _=>1,fun _=>zero_lt_one⟩

/-- Constructor earns all-clocks Paid, Literacy and Earned on *this* schedule and field family. Includes original CP5 house. -/
structure PaidP (a : Axis) (simple:G.Simple) (ε : ℝ) (s : OrderS G)
    (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T) : Prop where
    paid : WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W
    calculator : receipts R.kit
    realmP : FundedMarkedCoverRows.prices (combined (rows (prepared s)) (events (prepared s))) R.kit
    menu : Liner.PriceMenu R.kit

theorem original (a:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(O:OrderS G):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T), PaidP.{u} a simple ε O R T W := by
  let s:=prepared O
  let v := combined (rows s) (events s)
  let basic := @Together G (@FundedMarkedCoverRows.prices G v) (@WilsonReportColumnSubsidy.Eligible G)
  let extra := @Together G (@basic) (@Together G (@receipts G) (@Liner.PriceMenu G))
  have fees : WilsonFundedWindowMenu.AllPrices (@extra) := fun s q =>
    joint (joint (from_guard (of_prepaid (FundedMarkedCoverRows.purchase v s q)))
      (WilsonReportColumnSubsidy.allPrices s q)) (joint (buy s q) (Liner.issuer simple s q))
  obtain ⟨R,T,W,opening,seats,gates,patch,house,_,neutral,more,course,semester,stripsPaid,
    nested,panels,support,quiet,pub⟩ :=
    WilsonOriginalCollarWidthReceipt.original.{u} a (bound s.cap) (bound s.chronology)
      (increasing s.cap) simple positive law le_rfl
      (fun s _ => WilsonPhysicalHistoryPriorSelection.permitted MintClock.splits s _)
      (teacher s) (strips s) (bills s) (tube G) (@extra) fees
  refine ⟨R,T,W,?_,more.2.1,more.1.1,more.2.2⟩
  exact ⟨⟨_,course⟩,opening,seats,gates,patch,house,
    WilsonOriginalAllOrderFiledRealm.original (rows s) (events s) R simple more.1.1,neutral,
    course.2.1.2.1,more.1.2,semester,stripsPaid,nested,panels,support,quiet,
    fun cohort granted => WilsonOriginalAllOrderPublicFields.original (pub cohort granted)⟩

namespace PaidP
variable {a:Axis}{simple:G.Simple}{ε:ℝ}{s:OrderS G}
    {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}(p:PaidP.{u} a simple ε s R T W)
include p
lemma receiptsP : FundedOriginalProperties.{u} simple ε W ∧ WilsonWindowReportingPace.Slow R.kit := by
  obtain ⟨_,_,_,_,_,_,_,pace,_,_,_,fund,_⟩:=p.paid.originalSchool
  exact ⟨fund,pace⟩
lemma way : R2IGoals.Broad.{u} (garment10 G) W simple := p.receiptsP.1.2.1
lemma storageP : RG05Readout.Many.Storage R.family R.doors ∧ Cater R.family R.doors := WilsonCloseCaptureFinances.original R simple W (p.receiptsP.1)
lemma tuition : RG05Preconstruction.ReadoutPurchase R.b := p.receiptsP.1.2.2.2.2.2.2.1
lemma gear : WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels ∧
      WilsonReportLampForecast.Ready R.family.path.levels ∧ FundedOriginalVacuumPaths.prices R.kit := ⟨p.calculator.2.1,p.calculator.2.2,p.calculator.1⟩
end PaidP
end YM.Integration.Election
end
