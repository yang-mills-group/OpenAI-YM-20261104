import YM.SignedWilsonExpansion.Warehouse.Election
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7JointWeakBookPrices
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7OriginalWeakBookBudget

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


theorem _root_.PhysicalMatching.H7JointVisionWeakBookElection.original (a:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(O:OrderS G)
    (BB : Prediction G) (payBB : WilsonFundedWindowMenu.AllPrices (@BB)) :
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T), PaidP.{u} a simple ε O R T W ∧ BB R.kit := by
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
      (teacher s) (strips s) (bills s) (tube G) (@Together G (@extra) (@BB))
      (PhysicalMatching.H7JointWeakBookPrices.joint (@extra) (@BB) fees payBB)
  let old := more.1
  refine ⟨R,T,W,?_,more.2⟩
  refine ⟨?_,old.2.1,old.1.1,old.2.2⟩
  exact ⟨⟨_,course⟩,opening,seats,gates,patch,house,
    WilsonOriginalAllOrderFiledRealm.original (rows s) (events s) R simple old.1.1,neutral,
    course.2.1.2.1,old.1.2,semester,stripsPaid,nested,panels,support,quiet,
    fun cohort granted => WilsonOriginalAllOrderPublicFields.original (pub cohort granted)⟩

theorem _root_.PhysicalMatching.H7JointVisionWeakBookElection.atCosts (a : Axis)
    (simple : G.Simple) {ε : ℝ} (positive : 0 < ε) (O : OrderS G)
    (c : PhysicalMatching.H7JointWeakBookPrices.Costs G) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      PaidP.{u} a simple ε O R T W ∧ PhysicalMatching.H7OriginalWeakBookBudget.prediction c R.kit :=
  PhysicalMatching.H7JointVisionWeakBookElection.original a simple positive O
    (@PhysicalMatching.H7OriginalWeakBookBudget.prediction G c)
    (PhysicalMatching.H7OriginalWeakBookBudget.paid c)

end YM.Integration.Election
end
