import YM.Integration.CappedRegularReset

/-! Explicit finite-degree growth of the unchanged-shell regular bill.
The displayed coefficient depends only on Gauge, the two derivative orders,
and the fixed support exponent; it is independent of B and threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CappedRegularGrowth
open Lattice Wilson RG AnalyticBridge VerifiedReset Collection Geo
open Extra.Iteration Next.Scheduling CappedRegularReset
open scoped BigOperators
variable {G : Gauge}

def degree (p : BudgetPoint) : ℕ :=
  Geo.rowDegree p + Wages.grade 3 p.power p.order + Wages.grade 4 p.power p.order
def momentCoefficient (s : ℕ) : ℝ := Real.exp 1 * s.factorial
def lowCoefficient (G : Gauge) (p : BudgetPoint) : ℝ :=
  Quotes.anchoredFee p Geo.lowCount * lowCost G p 0 *
    momentCoefficient (Geo.rowDegree p) * Fintype.card PlaqAxes
def highCoefficient (G : Gauge) (p : BudgetPoint) : ℝ :=
  Quotes.anchoredFee p Geo.highCount *
    (Wages.startup G 3 p.power p.order * momentCoefficient (Wages.grade 3 p.power p.order) +
     Wages.startup G 4 p.power p.order * momentCoefficient (Wages.grade 4 p.power p.order))
def coefficient (G : Gauge) (p : BudgetPoint) : ℝ :=
  1 + Quotes.resetFee G p + Collection.turnFee p *
    (lowCoefficient G p + highCoefficient G p)

private lemma constants_nonnegative (G : Gauge) (p : BudgetPoint) :
    0 ≤ lowCoefficient G p ∧ 0 ≤ highCoefficient G p := by
  have hlow := low_nonneg G p 0
  have hs := Wages.slot_ge G p.power p.order 0
  unfold lowCoefficient highCoefficient momentCoefficient Quotes.anchoredFee Wages.startup
  constructor <;> positivity

theorem coefficient_positive (G : Gauge) (p : BudgetPoint) : 0 < coefficient G p := by
  obtain ⟨hl, hh⟩ := constants_nonnegative G p
  have hr : 0 < Quotes.resetFee G p := by
    unfold Quotes.resetFee
    exact mul_pos (Real.exp_pos _) (Residual.loss_pos G p)
  have ht := Collection.turnFee_pos p
  unfold coefficient
  positivity

/-- The cost itself ignores B and threshold when alpha is zero. -/
theorem regular_fields (G : Gauge) (p q : BudgetPoint) (c : Clip) (σ C H : ℝ)
    (hp : p.power = q.power) (ho : p.order = q.order)
    (hs : p.supportExponent = q.supportExponent) :
    CappedRegularReset.regularNeed G p c σ C 0 H =
      CappedRegularReset.regularNeed G q c σ C 0 H := by
  simp only [CappedRegularReset.regularNeed, abs_zero, zero_mul, zero_add,
    Quotes.resetFee, Residual.resetLoss, Residual.multiplier, pairBill,
    CappedRegularReset.lowBase, CappedRegularReset.lowFee,
    CappedRegularReset.highBase, CappedRegularReset.both, CappedRegularReset.highFee,
    Quotes.anchoredFee, Collection.turnFee, lowCost, faceCost, rowCost,
    Geo.rowDegree, hp, ho, hs]

private lemma moment_degree (p : BudgetPoint) (s : ℕ) (hd : s ≤ degree p)
    {σ : ℝ} (hσ : 0 < σ) :
    CappedRegularReset.moment s σ ≤
      momentCoefficient s * (1 + 2 * σ⁻¹) ^ degree p := by
  have hW : 1 ≤ 1 + 2 * σ⁻¹ :=
    le_add_of_nonneg_right (mul_nonneg (by norm_num) (inv_nonneg.mpr hσ.le))
  exact (CappedRegularReset.moment_bound s hσ).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW hd)
      (by positivity))

/-- A literal polynomial in original reciprocal width and path price. -/
theorem regular_growth (G : Gauge) (p : BudgetPoint) (c : Clip)
    {σ C H : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : c.direct ≤ 1) :
    CappedRegularReset.regularNeed G p c σ C 0 H ≤
      coefficient G p * (1 + 2 * σ⁻¹) ^ degree p * (1 + C ^ 2) * H := by
  let w := (1 + 2 * σ⁻¹) ^ degree p
  let z := 1 + C ^ 2
  have hw1 : 1 ≤ w := one_le_pow₀
    (le_add_of_nonneg_right (mul_nonneg (by norm_num) (inv_nonneg.mpr hσ.le)))
  have hw : 0 ≤ w := zero_le_one.trans hw1
  have hz1 : 1 ≤ z := by
    dsimp only [z]
    exact le_add_of_nonneg_right (sq_nonneg C)
  have hz : 0 ≤ z := zero_le_one.trans hz1
  have hlm := moment_degree p (Geo.rowDegree p) (by unfold degree; omega) hσ
  have h3 := moment_degree p (Wages.grade 3 p.power p.order) (by unfold degree; omega) hσ
  have h4 := moment_degree p (Wages.grade 4 p.power p.order) (by unfold degree; omega) hσ
  have hs (k : ℕ) : 0 ≤ Wages.startup G k p.power p.order := by
    have := Wages.slot_ge G p.power p.order 0
    unfold Wages.startup
    positivity
  have hm (k : ℕ) : 0 ≤ momentCoefficient k := by unfold momentCoefficient; positivity
  have ha (k : ℕ) : 0 ≤ Quotes.anchoredFee p k := by unfold Quotes.anchoredFee; positivity
  have hsize : Geo.lowerSize c C ≤ (Fintype.card PlaqAxes : ℝ) * z := by
    simpa only [Geo.lowerSize, z, pow_two] using
      mul_le_mul_of_nonneg_left (add_le_add hc (le_refl (C * C)))
        (Nat.cast_nonneg (Fintype.card PlaqAxes))
  have hsize0 : 0 ≤ Geo.lowerSize c C := by
    have := c.quadratic_pos
    unfold Geo.lowerSize
    positivity
  have hl : CappedRegularReset.lowBase G c p σ C ≤ lowCoefficient G p * w * z := by
    have ht := mul_le_mul
      (mul_le_mul_of_nonneg_left hlm (low_nonneg G p 0)) hsize hsize0
      (mul_nonneg (low_nonneg G p 0) (mul_nonneg (hm _) hw))
    have ht' := mul_le_mul_of_nonneg_left ht (ha Geo.lowCount)
    convert ht' using 1 <;> first
      | rfl
      | dsimp only [lowCoefficient, w]; ring
  have hf : CappedRegularReset.both G p σ ≤
      (Wages.startup G 3 p.power p.order * momentCoefficient (Wages.grade 3 p.power p.order) +
       Wages.startup G 4 p.power p.order * momentCoefficient (Wages.grade 4 p.power p.order)) * w := by
    have ht := add_le_add (mul_le_mul_of_nonneg_left h3 (hs 3))
      (mul_le_mul_of_nonneg_left h4 (hs 4))
    convert ht using 1 <;> first
      | rfl
      | dsimp only [w]; ring
  have hc2 : C + C ≤ z := by dsimp [z]; nlinarith [sq_nonneg (C - 1)]
  have hh : CappedRegularReset.highBase G p σ C ≤ highCoefficient G p * w * z := by
    have ht := mul_le_mul hf hc2 (add_nonneg hC hC)
      (mul_nonneg (add_nonneg (mul_nonneg (hs 3) (hm _)) (mul_nonneg (hs 4) (hm _))) hw)
    have ht' := mul_le_mul_of_nonneg_left ht (ha Geo.highCount)
    convert ht' using 1 <;> first
      | rfl
      | dsimp only [highCoefficient]; ring
  have hr : 0 ≤ Quotes.resetFee G p := by
    unfold Quotes.resetFee
    exact mul_nonneg (Real.exp_pos _).le (Residual.loss_pos G p).le
  have ht := (Collection.turnFee_pos p).le
  have hr' : Quotes.resetFee G p ≤ Quotes.resetFee G p * w * z := by
    have h1 := mul_le_mul_of_nonneg_left hw1 hr
    have h2 := mul_le_mul_of_nonneg_left hz1 (mul_nonneg hr hw)
    have h1' : Quotes.resetFee G p ≤ Quotes.resetFee G p * w := by
      simpa only [mul_one] using h1
    have h2' : Quotes.resetFee G p * w ≤ Quotes.resetFee G p * w * z := by
      simpa only [mul_one] using h2
    exact h1'.trans h2'
  have hquote : Quotes.resetFee G p + Collection.turnFee p *
      (CappedRegularReset.lowBase G c p σ C + CappedRegularReset.highBase G p σ C) ≤
      coefficient G p * w * z := by
    calc
      _ ≤ Quotes.resetFee G p * w * z + Collection.turnFee p *
          (lowCoefficient G p * w * z + highCoefficient G p * w * z) :=
        add_le_add hr' (mul_le_mul_of_nonneg_left (add_le_add hl hh) ht)
      _ = (Quotes.resetFee G p + Collection.turnFee p *
          (lowCoefficient G p + highCoefficient G p)) * w * z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by unfold coefficient; linarith) hw) hz
  have hfinal := mul_le_mul_of_nonneg_right hquote hH
  dsimp only [w, z] at hfinal
  convert hfinal using 1 <;> first
    | rfl
    | simp only [CappedRegularReset.regularNeed, abs_zero, zero_mul, zero_add]; ring

end YM.Integration.CappedRegularGrowth
end
