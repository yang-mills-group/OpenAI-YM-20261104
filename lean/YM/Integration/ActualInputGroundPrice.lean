import YM.Integration.ActualInputPatternPrice
import YM.Integration.ActualGaussianRowPrice
import YM.Integration.FullQLocalNumericLogarithmicCost

/-! The original centered ground coefficient is polynomially paid.
The constant, exponent and event precede all data and every retained positive
order. The exact normalized vertices, original Gaussian covariance and actual
one-bond field are those used in the full connected expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualInputGroundPrice
open Function Filter Lattice Wilson RG Precision Tree Exterior Marker
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Push.Uniform RG08.Line Comparison.RG02 PhysicalNext.Repeat.Legato
open FiniteVacuumProgramBound
open scoped Topology BigOperators Classical

private def orderBudget (r : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (r + 1), orderConstant n

private theorem order_nonneg (n : ℕ) : 0 ≤ orderConstant n := by
  unfold orderConstant
  positivity

private theorem orderBudget_pos (r : ℕ) : 0 < orderBudget r := by
  have h := Finset.sum_nonneg (s := Finset.range (r + 1))
    (fun n _ => order_nonneg n)
  unfold orderBudget
  linarith

private theorem order_le {n r : ℕ} (h : n ≤ r) : orderConstant n ≤ orderBudget r := by
  have hs := Finset.single_le_sum (fun k _ => order_nonneg k)
    (Finset.mem_range.mpr (show n < r + 1 by omega))
  exact hs.trans (le_add_of_nonneg_left zero_le_one)

private theorem one_side {G : Gauge} {V : Type} {T : Run G} {J : Request V}
    (A : NumericSchedule T.family J) {C : ℝ} (hC : 0 ≤ C) (e i : ℕ)
    (h : C * Real.log (T.family.path.levels.clock.hatBeta i) ^ e +
      C * Real.log (T.family.path.levels.clock.hatBeta (i + 1)) ^ e ≤ A.admittedCost i) :
    C * Real.log (T.family.path.levels.clock.hatBeta i) ^ e ≤ A.admittedCost i := by
  have hn := mul_nonneg hC
    (pow_nonneg (Real.log_pos (T.family.path.levels.fits.delayed (i + 1))).le e)
  linarith

private theorem polynomial_bound {n r e : ℕ} (hn : n ≤ r)
    {C W A B D : ℝ} (hC : 0 ≤ C) (hW : 1 ≤ W)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hA : A ≤ (1 + C) * W ^ e) (hB : B ≤ 2 * W) (hD : D ≤ 2 * W) :
    orderConstant n * A ^ n * B ^ (3 * n) * D ^ (3 * n) ≤
      (orderBudget r * (1 + C) ^ r * 2 ^ (6 * r)) * W ^ (e * r + 6 * r) := by
  have hwe : 1 ≤ W ^ e := one_le_pow₀ hW
  have hab : 1 ≤ (1 + C) * W ^ e := by
    nlinarith [mul_nonneg hC (zero_le_one.trans hwe)]
  have htw : 1 ≤ 2 * W := by linarith
  have ha : A ^ n ≤ ((1 + C) * W ^ e) ^ r := by
    exact (pow_le_pow_left₀ hA0 hA n).trans (pow_le_pow_right₀ hab hn)
  have hb : B ^ (3 * n) ≤ (2 * W) ^ (3 * r) := by
    exact (pow_le_pow_left₀ hB0 hB _).trans
      (pow_le_pow_right₀ htw (Nat.mul_le_mul_left 3 hn))
  have hd : D ^ (3 * n) ≤ (2 * W) ^ (3 * r) := by
    exact (pow_le_pow_left₀ hD0 hD _).trans
      (pow_le_pow_right₀ htw (Nat.mul_le_mul_left 3 hn))
  calc
    _ ≤ orderBudget r * (((1 + C) * W ^ e) ^ r) *
        ((2 * W) ^ (3 * r)) * ((2 * W) ^ (3 * r)) := by
      have h0 := mul_le_mul (order_le hn) ha (pow_nonneg hA0 n)
        (orderBudget_pos r).le
      have h1 := mul_le_mul h0 hb (pow_nonneg hB0 _)
        (mul_nonneg (orderBudget_pos r).le
          (pow_nonneg (zero_le_one.trans hab) _))
      exact mul_le_mul h1 hd (pow_nonneg hD0 _)
        (mul_nonneg (mul_nonneg (orderBudget_pos r).le
          (pow_nonneg (zero_le_one.trans hab) _))
          (pow_nonneg (zero_le_one.trans htw) _))
    _ = _ := by
      rw [show 6 * r = 3 * r + 3 * r by omega]
      simp only [pow_add, mul_pow, pow_mul]
      ring

/-- One event and one polynomial pay all original positive-order ground
coefficients through the requested order, before cutoff, period and tests. -/
theorem ground_polynomial {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (A : NumericSchedule T.family J) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, ∀ᶠ i : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = i →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (x : TestSpace J.tests)
        (t : (T.family.path.levels.clock.op datum.level datum.period).Choices),
      let F := green (T.family.path.levels.clock.op datum.level datum.period)
      let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
      ∀ n : ℕ, 0 < n → n ≤ J.order →
        ‖Symmetry.Orbit.ground (datum.kernel Y) F t (I.colors x) J.order n B -
          Symmetry.Orbit.ground (datum.kernel Y) F t (I.colors x) J.order n 0‖ ≤
          C * (A.admittedCost i) ^ e := by
  obtain ⟨C, hC, e, h⟩ := ActualInputPatternPrice.patterns T hG hT (R := R) A
  let cb : ℝ := (Fintype.card (Stationary.Loc G 1) : ℝ) * Real.exp 8
  let cd : ℝ := 2 + (Fintype.card (Stationary.Loc G 1) : ℝ) * Real.exp 4
  have hcb : 0 ≤ cb := by dsimp only [cb]; positivity
  have hcd : 0 ≤ cd := by dsimp only [cd]; positivity
  let Cfinal := orderBudget J.order * (1 + C) ^ J.order * 2 ^ (6 * J.order)
  have hfinal : 0 < Cfinal := by
    have ho := orderBudget_pos J.order
    dsimp only [Cfinal]
    positivity
  refine ⟨Cfinal, hfinal, e * J.order + 6 * J.order, ?_⟩
  filter_upwards [h, A.logarithmic_cost hG cb 5, A.logarithmic_cost hG cd 6]
    with i hi hb hd
  intro datum hlevel Y I x t
  subst i
  dsimp only
  intro n hn hnr
  let F := green (T.family.path.levels.clock.op datum.level datum.period)
  let K := datum.kernel Y
  let W := A.admittedCost datum.level
  let L := Real.log (T.family.path.levels.clock.hatBeta datum.level)
  let price := 1 + C * W ^ e
  let rowPrice := 1 + cb * L ^ 5
  let D := ActualInputPatternPrice.rayCost T datum.level
  have hW : 1 ≤ W := A.admitted_cost_ge_one datum.level
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hL : 0 ≤ L := (Real.log_pos (T.family.path.levels.fits.delayed _)).le
  have hprice : 1 ≤ price := by
    dsimp only [price]
    linarith [mul_nonneg hC.le (pow_nonneg hW0 e)]
  have hrow : 1 ≤ rowPrice := by
    dsimp only [rowPrice]
    linarith [mul_nonneg hcb (pow_nonneg hL 5)]
  have hD : 1 ≤ D := by
    change 1 ≤ 1 + cd * L ^ 6
    linarith [mul_nonneg hcd (pow_nonneg hL 6)]
  have hp := hi datum rfl Y I x t
  have hp' : PatternPrice (ActualGroundProgram.coupling F) (Bulk.hinge F)
      (ActualGroundContraction.rayMap K F
        (NativeNormalizedBondTest.actualField T hG datum.level datum.period))
      (Bulk.geometric K F t (I.colors x)) n price D := by
    exact ⟨fun j hj hjn => hp.physical j hj (hjn.trans hnr),
      fun j hj hjn => hp.gaussian j hj (hjn.trans hnr)⟩
  have hr (a : Precision.Key F G) :
      (∑ j, ‖(YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
        (K.covariance F t) (K.symm F t)).cov a j‖) ≤ rowPrice := by
    have hraw := ActualGaussianRowPrice.row_bound T Y hT datum.cutoff
      datum.period datum.level datum.below t a
    exact hraw.trans (le_add_of_nonneg_left zero_le_one)
  have hg := ground_centered_bound K F t (I.colors x) J.order hn hnr
    (NativeNormalizedBondTest.actualField T hG datum.level datum.period)
    price rowPrice D hprice hrow hD hp' hr
  have hb' : cb * L ^ 5 ≤ W := one_side A hcb 5 _ hb
  have hd' : cd * L ^ 6 ≤ W := one_side A hcd 6 _ hd
  have hwe : 1 ≤ W ^ e := one_le_pow₀ hW
  have ha' : price ≤ (1 + C) * W ^ e := by
    dsimp only [price]
    nlinarith
  have hb'' : rowPrice ≤ 2 * W := by dsimp only [rowPrice]; linarith
  have hd'' : D ≤ 2 * W := by
    change 1 + cd * L ^ 6 ≤ 2 * W
    linarith
  exact hg.trans (polynomial_bound hnr hC.le hW
    (zero_le_one.trans hprice) (zero_le_one.trans hrow) (zero_le_one.trans hD)
    ha' hb'' hd'')

end YM.Integration.ActualInputGroundPrice
end
