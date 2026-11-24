import YM.Integration.WilsonOriginalAllOrderFiledRealm
import YM.Integration.WilsonOriginalAllOrderPublicFields

/-! A single original hierarchy for all finite numerical programmes. The
physical external test, source coefficient and regulators enter after election. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalAllOrderCourse
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
open WilsonOriginalAllOrderCalendar
universe u
variable {G : Gauge}

/-- A finite numerical request is indexed by its full discrete specification.
All of these functions are installed once. They contain no realized period,
cutoff, marked amplitude, or assertion comparing correlation functions. -/
structure Schedule (G : Gauge) where
  cap : Key → ℕ
  chronology : Key → ℕ
  neutral : Key → Request G
  extraStrip : Key → WilsonOriginalSmallStrip.Menu G
  gearBill : Key → ℕ → Gear G → ℝ
  fixedDigit : Key → ℕ → WilsonIndependentCollarEventMenu.Request G

def index : ℕ → Key := list ([], 0, 0, 0, 0) id

theorem indexed (key : Key) : index (Encodable.encode key) = key := at_code _ id key

def bound (f : Key → ℕ) (j : ℕ) : ℕ := max j ((range (j+1)).sup (f ∘ index))

theorem increasing (f : Key → ℕ) : Monotone (bound f) := by
  intro i j h
  apply max_le (h.trans (le_max_left ..))
  apply Finset.sup_le
  intro q inRange
  exact (Finset.le_sup (f:=f ∘ index)
    (mem_range_succ_iff.mpr ((mem_range_succ_iff.mp inRange).trans h))).trans (le_max_right ..)

theorem covers (f : Key → ℕ) (key : Key) (j : ℕ) (h : Encodable.encode key ≤ j) :
    f key ≤ bound f j := by
  have paid := (Finset.le_sup (f:=f ∘ index) (mem_range_succ_iff.mpr h)).trans (le_max_right j _)
  simpa only [Function.comp_apply,indexed,bound] using paid

abbrev rows (s : Schedule G) (q : ℕ) := s.neutral (index q)
abbrev events (s : Schedule G) (j q : ℕ) := s.fixedDigit (index q) j
abbrev strips (s : Schedule G) (q : ℕ) := s.extraStrip (index q)
abbrev bills (s : Schedule G) (q : ℕ) := s.gearBill (index q)
abbrev teacher (s : Schedule G) := diagonal (rows s)
abbrev law := WilsonPhysicalHistoryPriorAperture.law G MintClock.splits
noncomputable abbrev tube (G : Gauge) := Classical.choice (Comparison.Density.Transport.tube_exists G)

/-- The leases and original mask/census seats are the actual ones on this
run. The public master retains its original phase and fixed-chamber bills. -/
structure Paid (a : Axis) (simple : G.Simple) (ε : ℝ) (s : Schedule G)
    (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T) : Prop where
  originalSchool : ∃ more : Prediction G,
    OnRun.{u} (bound s.cap) simple ε law (bound s.chronology) (@more) R T W
  first : WilsonOriginalCollarWidthReceipt.Open (teacher s) simple MintClock.splits R
  seats : ∀ k (S : Syl.School k), 2 ≤ S.order →
    ∀ᶠ m in atTop, WilsonOriginalCollarCensusSeats.Dated (teacher s) simple R S m
  books : WilsonOriginalCollarPhysicalBooks.Gates (teacher s) simple R
  patch : Covered (WilsonEmittedDictionary.program (tube G)) R
  house : House (teacher s) simple law R
  mint : WilsonOriginalAllOrderFiledRealm.Filed (rows s) (events s) R
  neutral : Neutral (teacher s) R.kit
  billsPaid : WilsonOriginalSeparatedElection.cover (bills s) R.kit
  reporter : WilsonReportColumnSubsidy.Eligible R.kit
  semester : WilsonOriginalSeparatedCalendar.Capped simple law R
  stripsPaid : WilsonOriginalSeparatedCalendar.Open (strips s) R
  nested : WilsonPositionProgramNestedElection.course simple a OPE.Stroke.epsilonR R.kit
  panels : R2I.RG05Joint.AcrossPanels R.kit
  support : ∀ i, (R.family.path.levels.budget i).supportExponent = 100
  quiet : WilsonOriginalSeparatedElection.Quiet R
  physical : ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
    (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
    ∀ v : Extraction.Order, WilsonOriginalAllOrderPublicFields.Master.{u} R simple cohort v

/-- Elect the run once for the whole programme of finite numerical requests.
On each requested extraction the complete physical master precedes every
roster, order, small radius, placed admitted input and regulator. -/
theorem original (a : Axis) (simple : G.Simple) {ε : ℝ} (positive : 0 < ε) (s : Schedule G) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), Paid.{u} a simple ε s R T W := by
  let v := combined (rows s) (events s)
  let extra := @Together G (@FundedMarkedCoverRows.prices G v) (@WilsonReportColumnSubsidy.Eligible G)
  have fees : AllPrices (@extra) :=
    fun s q => joint (from_guard (of_prepaid (FundedMarkedCoverRows.purchase v s q)))
      (WilsonReportColumnSubsidy.allPrices s q)
  obtain ⟨R,T,W,opening,seats,gates,patch,house,_,neutral,more,course,semester,stripsPaid,
    nested,panels,support,quiet,pub⟩ :=
    WilsonOriginalCollarWidthReceipt.original.{u} a (bound s.cap) (bound s.chronology)
      (increasing s.cap) simple positive law le_rfl
      (fun s _ => WilsonPhysicalHistoryPriorSelection.permitted MintClock.splits s _)
      (teacher s) (strips s) (bills s) (tube G) (@extra) fees
  exact ⟨R,T,W,⟨⟨_,course⟩,opening,seats,gates,patch,house,
    WilsonOriginalAllOrderFiledRealm.original (rows s) (events s) R simple more.1,neutral,
    course.2.1.2.1,more.2,semester,stripsPaid,nested,panels,support,quiet,
    fun cohort granted => WilsonOriginalAllOrderPublicFields.original (pub cohort granted)⟩⟩

end YM.Integration.WilsonOriginalAllOrderCourse
end
