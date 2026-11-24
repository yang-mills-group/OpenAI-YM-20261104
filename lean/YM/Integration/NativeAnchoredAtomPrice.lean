import YM.Integration.NativeAnchoredAtomBudget

/-! An explicit reciprocal-width polynomial for the actual one-port bill.
The coefficient depends only on the fixed gauge, rank cap and tensor order.
No upper bound on the original width and no period-dependent coefficient
is introduced. This is a bound on the displayed bill, not a new purchase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeAnchoredAtomPrice

open Push.Uniform NativeAtomTensorLocality NativeAnchoredAtomBudget
open MatchingLedger.Mountain
open scoped BigOperators

private def countCoefficient : ℝ := Real.exp 2 * (Nat.factorial 6 : ℝ) * 2 ^ 4

private def rootCoefficient (n : ℕ) : ℝ :=
  countCoefficient * (8 * ((n : ℝ) + 1)) ^ 6

private def freeCoefficient (G : Gauge) (n : ℕ) : ℝ :=
  (coordinateCount G : ℝ) * countCoefficient * (8 * ((n : ℝ) + 1) ^ 2) ^ 6

private def tensorCoefficient (G : Gauge) (cap n : ℕ) : ℝ :=
  (max 1 |Work.F02.slotConst G|) ^ cap *
    ((2 : ℝ) ^ (n + 2)) ^ n * (1 + |Miner.amount G n|) ^ n

def coefficient (G : Gauge) (cap d : ℕ) : ℝ :=
  rootCoefficient (d + 1) * tensorCoefficient G cap (d + 1) *
    freeCoefficient G (d + 1) ^ d

private theorem inverse_rate {width : ℝ} (hw : 0 < width) (n : ℕ) :
    (rate n width)⁻¹ ≤ 4 * ((n : ℝ) + 1) * (1 + width⁻¹) := by
  have hc : 0 < 4 * ((n : ℝ) + 1) := by positivity
  by_cases h : width / (4 * ((n : ℝ) + 1)) ≤ 1
  · rw [rate, min_eq_left h]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    exact mul_le_mul_of_nonneg_left (by linarith : width⁻¹ ≤ 1 + width⁻¹) hc.le
  · rw [rate, min_eq_right (le_of_not_ge h), inv_one]
    have hu : (1 : ℝ) ≤ 1 + width⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr hw.le)
    have hn : (1 : ℝ) ≤ 4 * ((n : ℝ) + 1) := by nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    simpa only [one_mul] using mul_le_mul hn hu zero_le_one hc.le

private theorem count_bound {x R : ℝ} (hx : 0 < x) (h1 : x ≤ 1) (hi : x⁻¹ ≤ R) :
    countCost x ≤ countCoefficient * R ^ 6 := by
  have he : Real.exp (x * 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
  have hp : (x⁻¹) ^ 6 ≤ R ^ 6 := pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hi 6
  have hc : 0 ≤ (Nat.factorial 6 : ℝ) := by positivity
  unfold countCost
  rw [div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ Real.exp 2 * (Nat.factorial 6 : ℝ) * R ^ 6 * 2 ^ 4 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right he hc) hp (by positivity) (by positivity))
        (by positivity)
    _ = _ := by unfold countCoefficient; ring

private theorem root_count {width : ℝ} (hw : 0 < width) (n : ℕ) :
    countCost (rate n width / 2) ≤ rootCoefficient n * (1 + width⁻¹) ^ 6 := by
  have hr : 0 < rate n width := by unfold rate; positivity
  have hr1 : rate n width ≤ 1 := min_le_right _ _
  have hi : (rate n width / 2)⁻¹ ≤ 8 * ((n : ℝ) + 1) * (1 + width⁻¹) := by
    calc
      _ = 2 * (rate n width)⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      _ ≤ 2 * (4 * ((n : ℝ) + 1) * (1 + width⁻¹)) :=
        mul_le_mul_of_nonneg_left (inverse_rate hw n) (by norm_num)
      _ = _ := by ring
  have h := count_bound (half_pos hr) (by linarith : rate n width / 2 ≤ 1) hi
  exact h.trans_eq (by unfold rootCoefficient; rw [mul_pow]; ring)

private theorem free_count {width : ℝ} (hw : 0 < width) (G : Gauge) (n : ℕ) :
    (coordinateCount G : ℝ) * countCost (weaker n (rate n width)) ≤
      freeCoefficient G n * (1 + width⁻¹) ^ 6 := by
  have hr : 0 < rate n width := by unfold rate; positivity
  have hr1 : rate n width ≤ 1 := min_le_right _ _
  have hd : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hb : 0 < weaker n (rate n width) := by unfold weaker; positivity
  have hb1 : weaker n (rate n width) ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hi : (weaker n (rate n width))⁻¹ ≤
      8 * ((n : ℝ) + 1) ^ 2 * (1 + width⁻¹) := by
    calc
      _ = (2 * ((n : ℝ) + 1)) * (rate n width)⁻¹ := by
        simp only [weaker, div_eq_mul_inv, mul_inv_rev, inv_inv]
      _ ≤ (2 * ((n : ℝ) + 1)) * (4 * ((n : ℝ) + 1) * (1 + width⁻¹)) :=
        mul_le_mul_of_nonneg_left (inverse_rate hw n) hd.le
      _ = _ := by ring
  have h := mul_le_mul_of_nonneg_left (count_bound hb hb1 hi)
    (show (0 : ℝ) ≤ coordinateCount G from Nat.cast_nonneg _)
  exact h.trans_eq (by unfold freeCoefficient; rw [mul_pow]; ring)

private theorem tensor_bound {width : ℝ} (hw : 0 < width) (G : Gauge) (cap n : ℕ) :
    NativeRestoredJetBudget.factor G cap n (width / 2) ≤
      tensorCoefficient G cap n * (1 + width⁻¹) ^ n := by
  have he : 1 + (2 : ℝ) ^ (n + 1) / (width / 2) =
      1 + (2 : ℝ) ^ (n + 2) * width⁻¹ := by
    have hp : (2 : ℝ) ^ (n + 1) * 2 = (2 : ℝ) ^ (n + 2) := by
      simpa only [Nat.add_assoc] using (pow_succ (2 : ℝ) (n + 1)).symm
    rw [div_div_eq_mul_div, hp, div_eq_mul_inv]
  have hc : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 2) := by
    simpa only [pow_zero] using
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 0 ≤ n + 2 by omega))
  have hb : 1 + (2 : ℝ) ^ (n + 2) * width⁻¹ ≤
      (2 : ℝ) ^ (n + 2) * (1 + width⁻¹) := by nlinarith
  unfold NativeRestoredJetBudget.factor
  rw [he]
  calc
    _ ≤ (max 1 |Work.F02.slotConst G|) ^ cap *
        ((2 : ℝ) ^ (n + 2) * (1 + width⁻¹)) ^ n * (1 + |Miner.amount G n|) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb n) (by positivity))
        (by positivity)
    _ = _ := by unfold tensorCoefficient; rw [mul_pow]; ring

/-- The complete one-port bill has a fixed reciprocal-width degree. -/
theorem port_polynomial (G : Gauge) (cap d : ℕ) {width : ℝ} (hw : 0 < width) :
    portFactor G cap d width ≤ coefficient G cap d * (1 + width⁻¹) ^ (7 * (d + 1)) := by
  have hr := root_count hw (d + 1)
  have ht := tensor_bound hw G cap (d + 1)
  have hf := free_count hw G (d + 1)
  have ha : 0 < rate (d + 1) width := by unfold rate; positivity
  have hb : 0 < weaker (d + 1) (rate (d + 1) width) := by unfold weaker; positivity
  have hfree : 0 ≤ (coordinateCount G : ℝ) * countCost (weaker (d + 1) (rate (d + 1) width)) :=
    mul_nonneg (Nat.cast_nonneg _) (count_pos hb).le
  have htc : 0 ≤ tensorCoefficient G cap (d + 1) * (1 + width⁻¹) ^ (d + 1) := by
    unfold tensorCoefficient
    positivity
  have hrc : 0 ≤ rootCoefficient (d + 1) * (1 + width⁻¹) ^ 6 := by
    unfold rootCoefficient countCoefficient
    positivity
  have hfg : 0 ≤ NativeRestoredJetBudget.factor G cap (d + 1) (width / 2) := by
    unfold NativeRestoredJetBudget.factor
    positivity
  unfold portFactor
  calc
    _ ≤ (rootCoefficient (d + 1) * (1 + width⁻¹) ^ 6) *
        (tensorCoefficient G cap (d + 1) * (1 + width⁻¹) ^ (d + 1)) *
        (freeCoefficient G (d + 1) * (1 + width⁻¹) ^ 6) ^ d :=
      mul_le_mul (mul_le_mul hr ht hfg hrc)
        (pow_le_pow_left₀ hfree hf d) (pow_nonneg hfree d) (mul_nonneg hrc htc)
    _ = _ := by
      unfold coefficient
      rw [mul_pow, ← pow_mul]
      have hdeg : 7 * (d + 1) = 6 + (d + 1) + 6 * d := by omega
      simp only [hdeg, pow_add]
      ring

/-- The coefficient is chosen before the width, period, roots and tensors. -/
theorem exists_port_polynomial (G : Gauge) (cap d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ width : ℝ, 0 < width →
      portFactor G cap d width ≤ C * (1 + width⁻¹) ^ (7 * (d + 1)) := by
  refine ⟨1 + |coefficient G cap d|, by positivity, ?_⟩
  intro width hw
  exact (port_polynomial G cap d hw).trans
    (mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self (coefficient G cap d)] : coefficient G cap d ≤ 1 + |coefficient G cap d|)
      (by positivity))

end YM.Integration.NativeAnchoredAtomPrice
end
