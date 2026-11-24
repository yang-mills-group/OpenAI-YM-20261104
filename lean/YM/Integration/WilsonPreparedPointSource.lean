import YM.Integration.SelectedWilsonForward
import YM.Integration.WilsonStartupJointMoment
import YM.Integration.ActualOriginalQInitialPreparation

/-! The concrete prepared Q source and the resolved coarse analytic model
share the very same physical Wilson forward conditional expectation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPreparedPointSource
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch LocalComparison LocalComparison.Global
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open MergeProof MergeProof.Accent SelectedWilsonForward
open scoped Classical BigOperators Topology
variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V) (A : NumericSchedule R.family J)
    (d : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V → ℕ)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "clock₀" => μ-R.family.S.scale d.cutoff
local notation "c₀" => ActualOriginalQInitialInput.scales R hG u J A d Q o μ orders
local notation "W₁" => R.family.path.rep d.cutoff d.period (d.level+1)

omit [DecidableEq V] [Nonempty V] in
/-- All actual basis references precede the fine step on a single common tail. -/
theorem ready : ∀ᶠ m : ℕ in atTop, ∀ j : ActualOriginalQReaders.Slot u, R.family.ref j.2.size ≤ m+1 := by
  let a := ∑ j : ActualOriginalQReaders.Slot u,R.family.ref j.2.size
  filter_upwards [eventually_ge_atTop a] with m hm
  intro j
  exact (Finset.single_le_sum (fun i (_ : i∈(univ : Finset (ActualOriginalQReaders.Slot u))) => Nat.zero_le (R.family.ref i.2.size)) (mem_univ j)).trans (hm.trans (Nat.le_succ m))

/-- Every complete signed combination of the actual chosen input polynomial
has the single measured whole Q startup as its normalized physical source. -/
theorem actual (top : d.cutoff=d.level+1) (href : ∀ j : ActualOriginalQReaders.Slot u,R.family.ref j.2.size ≤ d.level+1)
    (c : (Stock.census V).Mode → ℂ) (x : TestSpace (J₀).tests) (U : Config G (R.family.side (d.level+1) d.period)) :
    SelectedWilsonForward.read c (((ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders).leaf x).density U) =
      (W₁).eval U • WilsonStartupJointMoment.field Q D₀ u clock₀ orders c (VariableScaling.tests c₀ x) U := by
  rw [ActualOriginalQInitialPreparation.input_density,SelectedWilsonForward.value]
  have end_input (n : ℕ) (hn : d.level+1 ≤ n) (e : n=d.level+1) :
      ((ActualOriginalQInput.input Q D₀ u clock₀ orders hG n hn).leaf (VariableScaling.tests c₀ x)).density U =
        ((ActualOriginalQInput.input Q D₀ u clock₀ orders hG (d.level+1) le_rfl).leaf (VariableScaling.tests c₀ x)).density U := by
    subst n
    rfl
  rw [end_input d.cutoff (Nat.succ_le_of_lt d.below) top]
  have h := congrFun (WilsonStartupJointMoment.original Q D₀ u clock₀ orders hG href c (VariableScaling.tests c₀ x)) U
  simpa only [WilsonStartupJointMoment.source,top] using h

/-- The full physical source and the actual selected model are both specified;
there is no equality hypothesis about the analytic input or its representative. -/
theorem selected (hStage : WithStage R.metals.p OriginalRunConstruction.originalOrders)
    (hm : ActualOriginalQInitialPreparation.start R hG u J A hStage ≤ d.level)
    (hp : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val) (top : d.cutoff=d.level+1) (T : Campaign R)
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain R.family.path}
    {K : NumericPrices (A₀)} {M : FullQLocal.RenderedStep.Numeric.AnalyticOutput caps Y K
      (ActualOriginalQInitialPreparation.analyticInput R hG u J A d Q o μ orders hStage hm hp)} (S : FullQLocal.RenderedStep.Numeric.Retained.Chosen K
      (ActualOriginalQInitialPreparation.prepared R hG u J A d Q o μ orders hStage hm hp top T) M)
    (href : ∀ j : ActualOriginalQReaders.Slot u,R.family.ref j.2.size ≤ d.level+1)
    (c : (Stock.census V).Mode → ℂ) (x : TestSpace (J₀).tests) (W : Config G (R.family.side d.level d.period)) :
    SelectedWilsonForward.read c (ActualSelectedModelIntegral.defect S x W) =
      actualAverage R.family (N:=d.cutoff) (WilsonStartupJointMoment.field Q D₀ u clock₀ orders c (VariableScaling.tests c₀ x)) W-
        SelectedWilsonForward.read c (S.output.modelValue x W) := by
  let I := ActualOriginalQInitialPreparation.prepared R hG u J A d Q o μ orders hStage hm hp top T
  have eq_input := (ActualOriginalQInitialPreparation.prepared_fields R hG u J A d Q o μ orders hStage hm hp top T).2.1
  have pre (U : Config G (R.family.side (d.level+1) d.period)) :
      SelectedWilsonForward.read c ((I.input.leaf x).density U) = (W₁).eval U •
        WilsonStartupJointMoment.field Q D₀ u clock₀ orders c (VariableScaling.tests c₀ x) U := by
    rw [eq_input]
    exact actual R hG u J A d Q o μ orders top href c x U
  exact SelectedWilsonForward.residual R.makes S x (SelectedWilsonForward.read c)
    (WilsonStartupJointMoment.field Q D₀ u clock₀ orders c (VariableScaling.tests c₀ x)) pre W

end YM.Integration.WilsonPreparedPointSource
