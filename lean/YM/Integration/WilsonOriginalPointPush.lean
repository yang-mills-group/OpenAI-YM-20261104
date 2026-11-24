import YM.Integration.WilsonOriginalPointNumerator
import YM.Integration.WilsonRootedTwoDateOldIdentity

/-! The first physical conditional uses one signed, projected, test-independent point-source numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct.Seed
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent ActualPolynomialContraction OPE.Therm
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ} (a : Seed R B V N p (m+1)) (hG : G.Simple)
local notation "Γ" => Stock.census V
local notation "topRep" => R.family.path.rep N p (m+2)
local notation "loRep" => R.family.path.rep N p (m+1)
local notation "step" => R.family.path.levels.clock.op (m+1) p
local notation "tests" => (ActualOriginalQPointSetup.request R a.labels a.request).tests

/-- The coefficient of the full higher test field is pulled through the same Wilson/Haar kernel. -/
theorem pushed_mode (visible : a.visible) (x : IndependentTests (tests)) (j : (Γ).Mode) (U : Config G (R.family.side (m+1) p)) :
    ((step).push (topRep).beta ((a.with_test x).numerator hG) U).part j=
      (∏i∈j.val,(x i).val 0)*((step).push (topRep).beta (a.point_unit.numerator hG) U).part j := by
  let z := ∏i∈j.val,(x i).val 0
  have ax := (a.with_test x).numerator_integrable hG visible
  have ay := a.point_unit.numerator_integrable hG visible
  have pull := (R.family.path.levels.transition_mass (m+1) p (topRep).beta)
  have source : (fun v=>((a.with_test x).numerator hG v).part j)=z • (fun v=>(a.point_unit.numerator hG v).part j) := funext (a.numerator_mode hG visible (testInclusion _ x) j)
  have old := congrFun (push_get pull ax j) U
  have unit := congrFun (push_get pull ay j) U
  have scalar := congrFun ((step).push_smul (fun v=>(a.point_unit.numerator hG v).part j) (topRep).beta z ((Poly.get j).integrable_comp ay)) U
  exact old.trans ((congrFun (congrArg ((step).push (topRep).beta) source) U).trans (scalar.trans (congrArg (z*·) unit.symm)))

/-- The actual nonterminal normalized density has the same test multiplier on every gauge configuration. -/
theorem response_mode (visible : a.visible) (x : IndependentTests (tests)) (j : (Γ).Mode) (U : Config G (R.family.side (m+1) p)) :
    ((a.with_test x).response hG (Nat.le_succ (m+1)) U).part j=(∏i∈j.val,(x i).val 0)*(a.point_unit.response hG (Nat.le_succ (m+1)) U).part j := by
  rw [(a.with_test x).pushed hG,a.point_unit.pushed hG]
  change (((loRep).eval U)⁻¹:ℝ) * (((step).push (topRep).beta ((a.with_test x).numerator hG) U).part j)= _
  have eqv := a.pushed_mode hG visible x j U
  rw [eqv]
  exact mul_left_comm _ _ _

omit [Nonempty V] in
theorem mode_bound (x : IndependentTests (tests)) (s : (Γ).Mode) : ‖∏i∈s.val,(x i).val 0‖≤1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _=> norm_nonneg _) (fun i _=>WilsonOriginalPointModes.root_bound (tests) x i)

end YM.Integration.WilsonRootedTwoDateProduct.Seed
