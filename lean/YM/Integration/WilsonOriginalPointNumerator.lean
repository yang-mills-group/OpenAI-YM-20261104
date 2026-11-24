import YM.Integration.WilsonOriginalPointUnitTest
import YM.Integration.WilsonRootedTwoDateSource

/-! All independent tests share one true physical numerator at a fixed unmasked OPE birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct.Seed
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Precision IterationFour IterationFour.Vacuum
open MergeProof MergeProof.Accent ActualPolynomialContraction Pert.Asymptotics OPE.Therm
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ} (a : Seed R B V N p m) (hG : G.Simple)
local notation "Γ" => Stock.census V
local notation "Y" => R.family.path.rep N p (m+1)
local notation "tests" => (ActualOriginalQPointSetup.request R a.labels a.request).tests
local notation "D" => ActualOriginalQPointSetup.pointDatum R a.request p (m+1) a.roots
local notation "raw₀" => ActualOriginalQInput.input a.prescription (D) a.labels (a.scale-R.family.S.scale N) a.degree hG N a.below

def with_test (x : IndependentTests (tests)) : Seed R B V N p m := {a with test:=x}
def point_unit : Seed R B V N p m := a.with_test (WilsonOriginalPointModes.unit (tests))

def numerator_at (x : TestSpace (tests)) (U : Config G (R.family.side (m+1) p)) :=
  ((ActualOriginalQInitialPreparation.input R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree).leaf x).density U

/-- Both the input radius and the point-source normalization are held fixed while every
ambient test is allowed to vary. No mode is separated from the genuine gauge numerator. -/
theorem numerator_mode (visible : a.visible) (x : TestSpace (tests)) (k : (Γ).Mode) (U : Config G (R.family.side (m+1) p)) :
    (a.numerator_at hG x U).part k=(∏i∈k.val,(x i).val 0)*(a.point_unit.numerator hG U).part k := by
  let c := ActualOriginalQInitialInput.scales R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree
  let base := (((raw₀).leaf (WilsonOriginalPointModes.calibration (ActualRunQlocalNativeTuple.orbit (D)))).density U).part k
  have tested (y : TestSpace (tests)) : (a.numerator_at hG y U).part k=((∏i∈k.val,c i)*(∏i∈k.val,(y i).val 0))*base := by
    have incoming := congrArg (fun q : Poly (Γ)=>q.part k) (ActualOriginalQInitialPreparation.input_density R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree y U)
    have raw_read := WilsonOriginalPointModes.raw_mode R hG a.request a.labels a.prescription a.roots (a.scale-R.family.S.scale N) a.degree a.below (ActualOriginalQLayout.reference_le R a.labels visible) (VariableScaling.tests c y) k U
    refine incoming.trans (raw_read.trans ?_)
    change (∏i∈k.val,c i*(y i).val 0)*base=_
    rw [Finset.prod_mul_distrib]
  let y₁ := testInclusion (tests) (WilsonOriginalPointModes.unit (tests))
  change (a.numerator_at hG x U).part k=(∏i∈k.val,(x i).val 0)*(a.numerator_at hG y₁ U).part k
  rw [tested x,tested y₁]
  have unit_one : (∏i∈k.val,(y₁ i).val 0)=1 := Finset.prod_eq_one (fun i _=>WilsonOriginalPointModes.unit_read (tests) i)
  rw [unit_one,mul_one]
  ring

local notation "Q₀" => ActualOriginalQInitialInput.packets R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree
local notation "Y₀" => R.family.path.rep N p (m+1)
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p (m+1)
local notation "x₀" => testInclusion _ a.test


/-- The full filed numerator can be projected through the physical Haar kernel. -/
theorem numerator_integrable (h : a.visible) : Integrable (a.numerator hG) (prior G (R.family.side (m+1) p)) := by
  let M := fun U=>Poly.pass ((Q₀).read (x₀) (g₀) U)
  have vac : Envelope (Y₀).eval := (Y₀).envelope (R.makes.wilson.represents N p (m+1) a.below).good
  have kit := QLocalNormalizedQBirth.unit R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree (g₀)
  have field : Envelope M := kit.multiplier_envelope (fun t U=>NativePaidPacketColors.read_summable kit
    (Currency.g_pos R.makes _ _ _ a.below).ne' t (g₀) U) (x₀)
  have raw : a.numerator hG=fun U=>(Y₀).eval U • M U := funext (QLocalNormalizedQBirth.source R hG a.labels a.request
    a.schedule a.datum a.prescription a.roots a.scale a.degree h (x₀))
  rw [raw]
  obtain ⟨L,bounded⟩ := field.cost
  obtain ⟨K,cap⟩ := vac.cost
  apply Integrable.of_bound (vac.meas.smul field.meas).aestronglyMeasurable (K*L)
  apply ae_of_all
  intro U
  change ‖(Y₀).eval U • M U‖ ≤ K*L
  rw [norm_smul]
  exact mul_le_mul (cap U) (bounded U) (norm_nonneg _) ((norm_nonneg _).trans (cap U))

end YM.Integration.WilsonRootedTwoDateProduct.Seed
