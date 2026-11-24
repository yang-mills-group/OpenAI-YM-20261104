import YM.Integration.WilsonOriginalPointPush

/-! The authentic first physical conditional on every ambient upper test before bounded restriction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct.Seed
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open IterationFour IterationFour.Vacuum
open MergeProof MergeProof.Accent ActualPolynomialContraction OPE.Therm
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ} (a : Seed R B V N p (m+1)) (hG : G.Simple)
local notation "Γ" => Stock.census V
local notation "topRep" => R.family.path.rep N p (m+2)
local notation "loRep" => R.family.path.rep N p (m+1)
local notation "step" => R.family.path.levels.clock.op (m+1) p
local notation "tests" => (ActualOriginalQPointSetup.request R a.labels a.request).tests

/-- The arbitrary ambient source is integrable on the original compact Wilson field. -/
theorem numerator_at_integrable (visible : a.visible) (x : TestSpace (tests)) :
    Integrable (a.numerator_at hG x) (prior G (R.family.side (m+2) p)) := by
  apply integrable_pi_iff.mpr
  intro k
  change Integrable (fun v=>(a.numerator_at hG x v).part k) _
  let z := ∏ i∈k.val,(x i).val 0
  have eqv : (fun v=>(a.numerator_at hG x v).part k)=z • (fun v=>(a.point_unit.numerator hG v).part k) := funext (a.numerator_mode hG visible x k)
  rw [eqv]
  exact ((Poly.get k).integrable_comp (a.point_unit.numerator_integrable hG visible)).const_mul z

/-- This is the original normalized Wilson push, evaluated on the actual ambient point source. -/
def ambient_response (x : TestSpace (tests)) := actualSignedTransport R.family (N:=N) (a.numerator_at hG x) (Nat.le_succ (m+1))

/-- Every ambient gauge-dependent mode factors at the common first interior age. -/
theorem ambient_mode (visible : a.visible) (x : TestSpace (tests)) (j : (Γ).Mode) (U : Config G (R.family.side (m+1) p)) :
    (a.ambient_response hG x U).part j=(∏i∈j.val,(x i).val 0)*(a.point_unit.response hG (Nat.le_succ (m+1)) U).part j := by
  let z := ∏i∈j.val,(x i).val 0
  have ax := a.numerator_at_integrable hG visible x
  have ay := a.point_unit.numerator_integrable hG visible
  have pull := R.family.path.levels.transition_mass (m+1) p (topRep).beta
  have source : (fun v=>(a.numerator_at hG x v).part j)=z • (fun v=>(a.point_unit.numerator hG v).part j) := funext (a.numerator_mode hG visible x j)
  have old := congrFun (push_get pull ax j) U
  have unit := congrFun (push_get pull ay j) U
  have scalar := congrFun ((step).push_smul (fun v=>(a.point_unit.numerator hG v).part j) (topRep).beta z ((Poly.get j).integrable_comp ay)) U
  have pushed : (((step).push (topRep).beta (a.numerator_at hG x) U).part j)=z*(((step).push (topRep).beta (a.point_unit.numerator hG) U).part j) := old.trans ((congrFun (congrArg ((step).push (topRep).beta) source) U).trans (scalar.trans (congrArg (z*·) unit.symm)))
  rw [ambient_response,actualSignedTransport_eq R.family R.makes a.below,gust_step R.family.path N p (m+2) (a.numerator_at hG x) (Nat.lt_succ_self (m+1)),gust_base,a.point_unit.pushed hG]
  change (((loRep).eval U)⁻¹:ℝ)*(((step).push (topRep).beta (a.numerator_at hG x) U).part j)=_
  rw [pushed];exact mul_left_comm _ _ _

theorem ambient_bounded (x : IndependentTests (tests)) : a.ambient_response hG (testInclusion _ x)=(a.with_test x).response hG (Nat.le_succ (m+1)) := rfl

end YM.Integration.WilsonRootedTwoDateProduct.Seed
