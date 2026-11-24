import YM.Integration.NativeKineticCalibration
import YM.Integration.CappedRegularGrowth

/-! Fixed-degree growth of the complete kinetic calibration price. The original
width and row exponents remain unchanged. Both regular and full-hit prices
are included; the coefficient ignores block size and coupling threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeKineticCalibrationPrice
open Lattice Wilson RG AnalyticBridge VerifiedReset Collection Geo
open Extra.Iteration Next.Scheduling
open Push.AbsoluteSums Push.AbsoluteSums.Animals
open NativeCappedKineticQuotes NativeKineticCalibration
open scoped BigOperators

private def tailCoefficient : ℝ := (Nat.factorial 4 : ℝ) * Real.exp 1 ^ 2
private def lowCoefficient (p : BudgetPoint) : ℝ :=
  Real.exp ((p.supportExponent + 1) * Geo.lowCount) *
    Fintype.card Signed * Fintype.card PlaqAxes * 16 * tailCoefficient
private def highCoefficient (p : BudgetPoint) : ℝ :=
  Real.exp ((p.supportExponent + 1) * Geo.highCount) *
    Fintype.card Signed * (ballCost 1 : ℝ) * tailCoefficient

def degree (p : BudgetPoint) : ℕ := CappedRegularGrowth.degree p + 5
def coefficient (G : Gauge) (p : BudgetPoint) : ℝ :=
  1 + CappedRegularGrowth.coefficient G p + 4 * lowCoefficient p + 16 * highCoefficient p

private theorem coefficients_nonnegative (p : BudgetPoint) :
    0 ≤ lowCoefficient p ∧ 0 ≤ highCoefficient p := by
  unfold lowCoefficient highCoefficient tailCoefficient
  constructor <;> positivity

theorem coefficient_positive (G : Gauge) (p : BudgetPoint) : 0 < coefficient G p := by
  obtain ⟨hl, hh⟩ := coefficients_nonnegative p
  have hg := CappedRegularGrowth.coefficient_positive G p
  unfold coefficient
  positivity

/-- The fixed coefficient is selected before B and threshold. -/
theorem fields (G : Gauge) (p q : BudgetPoint)
    (hp : p.power = q.power) (ho : p.order = q.order)
    (hs : p.supportExponent = q.supportExponent) :
    degree p = degree q ∧ coefficient G p = coefficient G q := by
  constructor
  · simp only [degree, CappedRegularGrowth.degree, Geo.rowDegree, hp, ho]
  · simp only [coefficient, lowCoefficient, highCoefficient,
      CappedRegularGrowth.coefficient, CappedRegularGrowth.lowCoefficient,
      CappedRegularGrowth.highCoefficient, CappedRegularGrowth.momentCoefficient,
      Quotes.resetFee, Residual.resetLoss, Residual.multiplier, pairBill,
      Quotes.anchoredFee, Collection.turnFee, lowCost, faceCost, rowCost,
      Geo.rowDegree, hp, ho, hs]

private theorem inverse_radius {σ : ℝ} (hσ : 0 < σ) :
    (hitRadius σ)⁻¹ ≤ 1 + 4 * σ⁻¹ := by
  by_cases h : σ / 4 ≤ 1
  · have he : (σ / 4)⁻¹ = 4 * σ⁻¹ := by field_simp [hσ.ne']
    rw [hitRadius, min_eq_left h, he]
    linarith
  · rw [hitRadius, min_eq_right (le_of_not_ge h), inv_one]
    linarith [inv_pos.mpr hσ]

private theorem inverse_tail {ε : ℝ} (hε : 0 < ε) (h1 : ε ≤ 1) :
    (1 - Real.exp (-ε))⁻¹ ≤ Real.exp 1 * ε⁻¹ := by
  have he : ε ≤ Real.exp ε - 1 := by linarith [Real.add_one_le_exp ε]
  have hf : 1 - (Real.exp ε)⁻¹ = (Real.exp ε - 1) / Real.exp ε := by
    rw [sub_div, div_self (Real.exp_pos ε).ne', one_div]
  calc
    _ = Real.exp ε / (Real.exp ε - 1) := by rw [Real.exp_neg, hf, inv_div]
    _ ≤ Real.exp ε / ε := div_le_div_of_nonneg_left (Real.exp_pos ε).le hε he
    _ ≤ Real.exp 1 / ε :=
      div_le_div_of_nonneg_right (Real.exp_monotone h1) hε.le
    _ = _ := div_eq_mul_inv _ _

private theorem hit_bound (W : ℕ) (a v γ : ℝ) (hγ : 0 ≤ γ)
    {σ : ℝ} (hσ : 0 < σ) :
    Footprint.payment 1 W 0 (hitRadius σ) 1 γ a v ≤
      Real.exp (a * v) * γ * (ballCost W : ℝ) * tailCoefficient *
        (1 + 4 * σ⁻¹) ^ 5 := by
  have hr : 0 < hitRadius σ := lt_min (by linarith) zero_lt_one
  have hr1 : hitRadius σ ≤ 1 := min_le_right _ _
  have ht : 0 < 1 - Real.exp (-hitRadius σ) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have he := mul_le_mul (Real.exp_monotone hr1) (inverse_tail hr hr1)
    (inv_nonneg.mpr ht.le) (Real.exp_pos 1).le
  have hc : 0 ≤ Real.exp (a * v) * γ * (ballCost W : ℝ) *
      (Nat.factorial 4 : ℝ) * (hitRadius σ)⁻¹ ^ 4 := by positivity
  have hp := mul_le_mul_of_nonneg_left he hc
  calc
    _ = (Real.exp (a * v) * γ * (ballCost W : ℝ) *
        (Nat.factorial 4 : ℝ) * (hitRadius σ)⁻¹ ^ 4) *
        (Real.exp (hitRadius σ) * (1 - Real.exp (-hitRadius σ))⁻¹) := by
      simp only [Footprint.payment, Footprint.degreeIncome, Footprint.spread,
        Nat.one_mul, Nat.add_zero, mul_one]
      ring
    _ ≤ (Real.exp (a * v) * γ * (ballCost W : ℝ) *
        (Nat.factorial 4 : ℝ) * (hitRadius σ)⁻¹ ^ 4) *
        (Real.exp 1 * (Real.exp 1 * (hitRadius σ)⁻¹)) := hp
    _ = Real.exp (a * v) * γ * (ballCost W : ℝ) * tailCoefficient *
        (hitRadius σ)⁻¹ ^ 5 := by unfold tailCoefficient; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hr.le) (inverse_radius hσ) 5)
      (by unfold tailCoefficient; positivity)

private theorem ball_bound (B : ℕ) :
    (ballCost B : ℝ) ≤ 16 * (1 + (B : ℝ)) ^ 4 := by
  simp only [ballCost, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ (2 * (1 + (B : ℝ))) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    _ = _ := by rw [mul_pow]; norm_num

private theorem full_growth (p : BudgetPoint) (c : Clip)
    {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C) (hc : c.direct ≤ 1) :
    fullCost c p σ C ≤ (4 * lowCoefficient p + 16 * highCoefficient p) *
      (1 + 4 * σ⁻¹) ^ 5 * (1 + C ^ 2) * (1 + (p.B : ℝ)) ^ 4 := by
  let w := 1 + 4 * σ⁻¹
  let z := 1 + C ^ 2
  let b := (1 + (p.B : ℝ)) ^ 4
  have hw : 0 ≤ w := by unfold w; positivity
  have hz : 0 ≤ z := by unfold z; positivity
  have hb : 1 ≤ b := one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg p.B))
  have hsize : Geo.lowerSize c C ≤ (Fintype.card PlaqAxes : ℝ) * z := by
    simpa only [Geo.lowerSize, z, pow_two] using
      mul_le_mul_of_nonneg_left (add_le_add hc (le_refl (C * C)))
        (Nat.cast_nonneg (Fintype.card PlaqAxes))
  have hsize0 : 0 ≤ Geo.lowerSize c C := by
    have := c.quadratic_pos
    unfold Geo.lowerSize
    positivity
  have hlow0 : 0 ≤ (Fintype.card Signed : ℝ) * Geo.lowerSize c C :=
    mul_nonneg (Nat.cast_nonneg _) hsize0
  have hl := hit_bound p.B (p.supportExponent + 1) Geo.lowCount
    (Fintype.card Signed * Geo.lowerSize c C) hlow0 hσ
  have hγ := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg (Fintype.card Signed))
  have hprod := mul_le_mul
    (mul_le_mul_of_nonneg_left hγ
      (Real.exp_pos ((p.supportExponent + 1) * Geo.lowCount)).le)
    (ball_bound p.B) (Nat.cast_nonneg (ballCost p.B))
    (by positivity)
  have hprod' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hprod (show 0 ≤ tailCoefficient from by unfold tailCoefficient; positivity)) (pow_nonneg hw 5)
  have hL : lowHitCost p c σ C ≤ lowCoefficient p * w ^ 5 * z * b := by
    refine hl.trans (hprod'.trans_eq ?_)
    unfold lowCoefficient w b
    ring
  have hhi0 : 0 ≤ (Fintype.card Signed : ℝ) * (C + C) := by positivity
  have hh := hit_bound 1 (p.supportExponent + 1) Geo.highCount
    (Fintype.card Signed * (C + C)) hhi0 hσ
  have hcz : C + C ≤ z := by unfold z; nlinarith [sq_nonneg (C - 1)]
  have hγh := mul_le_mul_of_nonneg_left hcz (Nat.cast_nonneg (Fintype.card Signed))
  have hprodH := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hγh
        (Real.exp_pos ((p.supportExponent + 1) * Geo.highCount)).le)
      (Nat.cast_nonneg (ballCost 1))) (show 0 ≤ tailCoefficient from by unfold tailCoefficient; positivity)
  have hprodH' := mul_le_mul_of_nonneg_right hprodH (pow_nonneg hw 5)
  have hH0 : highHitCost p σ C ≤ highCoefficient p * w ^ 5 * z := by
    refine hh.trans (hprodH'.trans_eq ?_)
    unfold highCoefficient w
    ring
  have hH : highHitCost p σ C ≤ highCoefficient p * w ^ 5 * z * b :=
    hH0.trans (le_mul_of_one_le_right
      (mul_nonneg (mul_nonneg (coefficients_nonnegative p).2 (pow_nonneg hw 5)) hz) hb)
  calc
    _ ≤ 4 * (lowCoefficient p * w ^ 5 * z * b) +
        16 * (highCoefficient p * w ^ 5 * z * b) :=
      add_le_add (mul_le_mul_of_nonneg_left hL (by norm_num))
        (mul_le_mul_of_nonneg_left hH (by norm_num))
    _ = _ := by unfold w z b; ring

private theorem regular_growth (G : Gauge) (p : BudgetPoint) (c : Clip)
    {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C) (hc : c.direct ≤ 1) :
    regularCost G c p σ C ≤ CappedRegularGrowth.coefficient G p *
      (1 + 2 * σ⁻¹) ^ CappedRegularGrowth.degree p * (1 + C ^ 2) := by
  have hm (k : ℕ) : 0 ≤ CappedRegularReset.moment k σ :=
    (momentPrice_pos k (lt_min (half_pos hσ) zero_lt_one)).le
  have hr := hm (Geo.rowDegree p)
  have h3 := hm (Wages.grade 3 p.power p.order)
  have h4 := hm (Wages.grade 4 p.power p.order)
  have hs := Wages.slot_ge G p.power p.order 0
  have hd := c.quadratic_pos
  have hn := low_nonneg G p 0
  have hl : 0 ≤ CappedRegularReset.lowBase G c p σ C := by
    unfold CappedRegularReset.lowBase CappedRegularReset.lowFee
      Quotes.anchoredFee Geo.lowerSize
    positivity
  have hh : 0 ≤ CappedRegularReset.highBase G p σ C := by
    unfold CappedRegularReset.highBase CappedRegularReset.both
      CappedRegularReset.highFee Quotes.anchoredFee Wages.startup
    positivity
  have ht := (Collection.turnFee_pos p).le
  have h2 : p.threshold ^ 2 ≤ 1 := pow_le_one₀ p.threshold_pos.le p.threshold_le
  have h3' : p.threshold ^ 3 ≤ 1 := pow_le_one₀ p.threshold_pos.le p.threshold_le
  have he : regularCost G c p σ C ≤ Collection.turnFee p *
      (CappedRegularReset.lowBase G c p σ C + CappedRegularReset.highBase G p σ C) := by
    calc
      _ = Collection.turnFee p *
          (p.threshold ^ 2 * CappedRegularReset.lowBase G c p σ C +
           p.threshold ^ 3 * CappedRegularReset.highBase G p σ C) := by
        unfold regularCost
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_of_le_one_left hl h2) (mul_le_of_le_one_left hh h3')) ht
  have hreset : 0 ≤ Quotes.resetFee G p := by
    unfold Quotes.resetFee
    exact mul_nonneg (Real.exp_pos _).le (Residual.loss_pos G p).le
  have hneed : Collection.turnFee p *
      (CappedRegularReset.lowBase G c p σ C + CappedRegularReset.highBase G p σ C) ≤
        CappedRegularReset.regularNeed G p c σ C 0 1 := by
    simp only [CappedRegularReset.regularNeed, abs_zero, zero_mul, zero_add, one_mul,
      mul_one]
    linarith
  have hg := CappedRegularGrowth.regular_growth G p c hσ hC zero_le_one hc
  exact (he.trans hneed).trans (by simpa only [mul_one] using hg)

/-- Complete regular/full-hit unit price, with no width upper bound. -/
theorem unitCost_polynomial (G : Gauge) (p : BudgetPoint) (c : Clip)
    {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C) (hc : c.direct ≤ 1) :
    NativeKineticCalibration.unitCost G c p σ C ≤ coefficient G p *
      (1 + 4 * σ⁻¹) ^ degree p * (1 + C ^ 2) * (1 + (p.B : ℝ)) ^ 4 := by
  let w := 1 + 4 * σ⁻¹
  let z := 1 + C ^ 2
  let b := (1 + (p.B : ℝ)) ^ 4
  have hw1 : 1 ≤ w := by unfold w; linarith [inv_pos.mpr hσ]
  have hw : 0 ≤ w := zero_le_one.trans hw1
  have hz : 0 ≤ z := by unfold z; positivity
  have hb : 1 ≤ b := one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg p.B))
  have hd : (1 + 2 * σ⁻¹) ^ CappedRegularGrowth.degree p ≤ w ^ degree p :=
    (pow_le_pow_left₀ (by positivity) (by unfold w; linarith [inv_pos.mpr hσ])
      (CappedRegularGrowth.degree p)).trans
      (pow_le_pow_right₀ hw1 (by unfold degree; omega))
  have h5 : w ^ 5 ≤ w ^ degree p :=
    pow_le_pow_right₀ hw1 (by unfold degree; omega)
  have hG := (CappedRegularGrowth.coefficient_positive G p).le
  obtain ⟨hL, hH⟩ := coefficients_nonnegative p
  have hr0 := (regular_growth G p c hσ hC hc).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hG) hz)
  have hr : regularCost G c p σ C ≤
      CappedRegularGrowth.coefficient G p * w ^ degree p * z * b :=
    hr0.trans (le_mul_of_one_le_right
      (mul_nonneg (mul_nonneg hG (pow_nonneg hw _)) hz) hb)
  have hf := (full_growth p c hσ hC hc).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h5 (by positivity)) hz)
      (zero_le_one.trans hb))
  calc
    _ ≤ CappedRegularGrowth.coefficient G p * w ^ degree p * z * b +
        (4 * lowCoefficient p + 16 * highCoefficient p) * w ^ degree p * z * b :=
      add_le_add hr hf
    _ = (CappedRegularGrowth.coefficient G p + 4 * lowCoefficient p +
        16 * highCoefficient p) * w ^ degree p * z * b := by ring
    _ ≤ coefficient G p * w ^ degree p * z * b :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by unfold coefficient; linarith)
            (pow_nonneg hw _)) hz) (zero_le_one.trans hb)
    _ = _ := rfl

end YM.Integration.NativeKineticCalibrationPrice
end
