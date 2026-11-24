import YM.Integration.WilsonOriginalCollarFiledRealm
import YM.Integration.WilsonOriginalSeparatedPublicFields

/-! The original physical selection pays the printed collar on one calendar. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCollarElection
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonFundedWindowCompany WilsonFundedWindowMenu WilsonWindowJointPurchase WilsonWindowBookPurchase
open WilsonReportingAbsoluteInletSchool WilsonWindowUniversalSchool
open FormalBulk08 FormalBulk08.Flat Push.PriceCompiler
open OPE.Owl WilsonCoeffUV WilsonCoeffUV.Bank
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {φ : ℕ → ℕ}

abbrev Neutral (request : WilsonOriginalCollarTeacher.Request G) := @WilsonOriginalProfileStrip.Filed G
  (WilsonOriginalCompoundStrip.programme (WilsonThermometerUnitFilingWeakStrip.enrolled request))

def law (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ) : VowsR.LawScroll G φ :=
  WilsonOlderFreshGraphMatrixPrice.jointLaw (WilsonOlderFreshGraphCommonHouse.course C split)

def requests (request : WilsonOriginalCollarTeacher.Request G) (simple : G.Simple)
    (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ) (extra : Prediction G) : Prediction G :=
  Together (@WilsonOlderFreshGraphSchool.grant G φ (WilsonOriginalCollarTeacher.menu request) simple (law C split))
    (Together (@FundedMarkedCoverRows.prices G (WilsonOriginalCollarTeacher.prices request))
      (Together (@Neutral G request) (@extra)))

theorem grant (request : WilsonOriginalCollarTeacher.Request G) (simple : G.Simple)
    (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted C s (ThroughLaunch.raging s q))
    (extra : Prediction G) (paid : AllPrices (@extra)) :
    AllPrices (@requests G φ request simple C split (@extra)) := by
  have graph := WilsonOlderFreshGraphSchool.before_period (WilsonOriginalCollarTeacher.menu request) simple
    (law C split) (fun s q => WilsonWindowVacuumLaws.both
      (WilsonWindowCourseLaws.physical_course split (permitted s q)) (WilsonPhysicalHistoryPriorSelection.permitted φ s _))
  intro s q
  exact joint (graph s q) (joint (from_guard
    (WilsonFundedWindowCompany.of_prepaid (FundedMarkedCoverRows.purchase _ s q)))
      (joint (WilsonOriginalProfileStrip.prepaid _ simple s _) (paid s q)))

/-- One choice of roots, rolls, books and forecast for every later enrollment.
The spring and court belong to this physical run. -/
def House (request : WilsonOriginalCollarTeacher.Request G) (simple : G.Simple)
    (C : VowsR.LawScroll G φ) (R : Run G) : Prop :=
  let D := WilsonOlderFreshGraphSchool.roots (WilsonOriginalCollarTeacher.menu request) simple R.metals.p R.metals.K
  let Q := WilsonOlderFreshGraphSchool.rollTab (WilsonOriginalCollarTeacher.menu request) simple R.metals R.rolls
  ∃ (B : Offices.Books D R.rolls Q φ) (F : Forecast D R.rolls Q φ B),
    Treehouse.VariableHouse R D Q C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p) ∧
    Oak.Semester R D Q B F ∧ VowsR.Chamber C R.kit D Q B ∧
    MintClock.Hospital D R.rolls Q R.kit.target φ B F R.alloy.delay ∧
    Spill.Raffle.Warm G D R.alloy.delay φ ∧ Scholar.Month R.rolls D Q R.alloy.delay ∧
    TicketP R.alloy R.kit D Q ∧
    WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay ∧
    ∀ k x, 1 ≤ k → Poetry.Agenda.seed D φ k x ≤ WilsonOriginalCollarTeacher.teacherWidth request R.metals.p.kernel x/16

theorem house (request : WilsonOriginalCollarTeacher.Request G) (simple : G.Simple)
    (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ) (R : Run G)
    (paid : WilsonOlderFreshGraphSchool.grant (WilsonOriginalCollarTeacher.menu request) simple (law C split) R.kit)
    (base : WilsonWindowVacuumAdmission.Ready R.kit) : House request simple C R := by
  let menu := WilsonOriginalCollarTeacher.menu request
  let D := WilsonOlderFreshGraphSchool.roots menu simple R.metals.p R.metals.K
  let Q := WilsonOlderFreshGraphSchool.rollTab menu simple R.metals R.rolls
  obtain ⟨⟨B, held⟩, widths⟩ := WilsonOlderFreshGraphSchool.on_run menu simple (law C split) R paid
  have core : VowsR.Chamber (WilsonOlderFreshGraphCommonHouse.course C split) R.kit D Q B :=
    {held with obligation := held.obligation.1}
  obtain ⟨F,physical⟩ := WilsonWindowUniversalSchool.house simple R D Q C B split core base
  refine ⟨B,F,physical,physical.licence.plan,physical.licence.employed,?_,core.obligation.2.2.2.1,
    ?_,paid.2,held.obligation.2,?_⟩
  · exact physical.licence.forecast
  · exact physical.licence.monthly
  intro k x hk
  apply (widths k x hk).trans
  simpa only [menu,WilsonOriginalCollarTeacher.menu,mul_one] using
    (div_le_div_of_nonneg_right (min_le_right ((WilsonOlderFreshGraphAllStages.menu G).width
      R.metals.p.profile R.metals.K R.metals.p.kernel k x) (WilsonOriginalCollarTeacher.teacherWidth
        request R.metals.p.kernel x)) (by norm_num : (0:ℝ)≤16))

theorem original (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap) (simple : G.Simple)
    {ε : ℝ} (positive : 0 < ε) (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted C s (ThroughLaunch.raging s q))
    (request : WilsonOriginalCollarTeacher.Request G)
    (additional : ℕ → WilsonOriginalSmallStrip.Menu G) (bills : ℕ → ℕ → Gear G → ℝ)
    (extra : Prediction G) (fund : AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      House request simple C R ∧ WilsonOriginalCollarFiledRealm.Filed request R ∧ Neutral request R.kit ∧
      extra R.kit ∧ OnRun.{u} cap simple ε C U (@WilsonOriginalSeparatedElection.demands G φ simple C split U bills
        (Together (@WilsonOriginalSmallStrip.Filed G (WilsonOriginalSeparatedCalendar.calendar additional))
          (@requests G φ request simple C split (@extra)))) R T W ∧
      WilsonOriginalSeparatedCalendar.Capped simple C R ∧ WilsonOriginalSeparatedCalendar.Open additional R ∧
      WilsonPositionProgramNestedElection.course simple a OPE.Stroke.epsilonR R.kit ∧
      R2I.RG05Joint.AcrossPanels R.kit ∧ (∀ i, (R.family.path.levels.budget i).supportExponent=100) ∧
      WilsonOriginalSeparatedElection.Quiet R ∧ ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
        WilsonMacroscopicFundedReader.Elected.{u} R simple cohort := by
  obtain ⟨R,T,W,school,prior,strips,nested,panels,alpha,quiet,geometry⟩ :=
    WilsonOriginalSeparatedCourse.original.{u} a cap U mono simple positive C split permitted additional bills
      (@requests G φ request simple C split (@extra)) (grant request simple C split permitted (@extra) fund)
  have sale := school.2.1.2.2.2.2
  exact ⟨R,T,W,house request simple C split R sale.1 school.2.1.1.2,
    WilsonOriginalCollarFiledRealm.original R simple request sale.2.1,sale.2.2.1,sale.2.2.2,
    school,prior,strips,nested,panels,alpha,quiet,geometry⟩

end YM.Integration.WilsonOriginalCollarElection
end
