import YM.Integration.FVA1Physical.Wilson.ResetPrice

/-! Ultraviolet rate for the kinetic reset comparison on the same run.
The source and the price are independent of the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter RG PhysicalNext.Repeat.Legato AnalyticBridge.VerifiedReset
open scoped Topology BigOperators

variable {G : Gauge} (A : Run G)

/-- The physical threshold and the pre-existing forecast leave an additional
one-fifth power of the calendar coupling in the reset error. -/
theorem reset_uv_bound (j : ℕ) :
    0 ≤ resetPrice A j ∧ resetPrice A j ≤ (64:ℝ)⁻¹ * (A.alloy.B.a.clock.hatCoupling j)^((1:ℝ)/5) := by
  let a := A.alloy.B.a
  let g := a.clock.hatCoupling j
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (a.fits.delayed j)))
  have ht := (a.budget j).threshold_pos
  have hw : g ≤ (a.budget j).threshold := le_mul_of_one_le_right hg.le (Real.one_le_exp (sq_nonneg _))
  have ha : a.clock.allowance j = g^((1:ℝ)/5)*g^2 := by
    change g^((11:ℝ)/5)=_
    rw [← Real.rpow_natCast, ← Real.rpow_add hg]
    norm_num
  have he : 0 ≤ Time.forecastE a j := mul_nonneg (Time.credit_pos G (a.params j)).le (Real.rpow_nonneg hg.le _)
  refine ⟨le_min (A.kit.post.rad_pos _ _).le (div_nonneg he (sq_nonneg _)),
    (min_le_right _ _).trans ((div_le_iff₀ (pow_pos ht 2)).mpr ?_)⟩
  change Time.credit G (a.params j)*a.clock.allowance j ≤ _ * (a.budget j).threshold^2
  rw [ha, ← mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (Time.authorized G (a.params j)).1 (Real.rpow_nonneg hg.le _))
    (pow_le_pow_left₀ hg.le hw 2) (sq_nonneg _) (by positivity)

/-- The error on any finite window is the sum of the physical reset prices. -/
theorem historyResetPrice_sum {m N : ℕ} (hm : m ≤ N) :
    historyResetPrice A m N = ∑ j ∈ Finset.Ico m N, resetPrice A j := by
  change (∑ j ∈ Finset.range N, resetPrice A j) - (∑ j ∈ Finset.range m, resetPrice A j) = _
  rw [← Finset.sum_range_add_sum_Ico _ hm]
  abel

private theorem reset_vanishes (hs : G.Simple) : Tendsto (resetPrice A) atTop (𝓝 0) := by
  let a := A.alloy.B.a
  have hβ : Tendsto a.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hs))
  have hg : Tendsto a.clock.hatCoupling atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hβ)
  have hp := (hg.rpow_const (p := (1:ℝ)/5) (Or.inr (by norm_num))).const_mul (64:ℝ)⁻¹
  apply squeeze_zero (fun j => (reset_uv_bound A j).1) (fun j => (reset_uv_bound A j).2)
  simpa only [Real.zero_rpow (show (1:ℝ)/5 ≠ 0 by norm_num), mul_zero] using hp

/-- On every fixed-width ultraviolet window the entire reset discrepancy tends
to zero uniformly in the period, including the exact physical tuning. -/
theorem fixed_window_resets_vanish (hs : G.Simple) (length : ℕ) :
    Tendsto (fun m => historyResetPrice A m (m+length)) atTop (𝓝 0) := by
  induction length with
  | zero =>
    simpa only [Nat.add_zero,historyResetPrice,sub_self] using (tendsto_const_nhds (f:=atTop) (x:=(0:ℝ)))
  | succ length ih =>
    have ht := (reset_vanishes A hs).comp (tendsto_add_atTop_nat length)
    have he (m : ℕ) : historyResetPrice A m (m+(length+1)) =
        historyResetPrice A m (m+length) + resetPrice A (m+length) := by
      change (∑ j ∈ Finset.range (m+length+1), resetPrice A j) - (∑ j ∈ Finset.range m, resetPrice A j) =
        ((∑ j ∈ Finset.range (m+length), resetPrice A j) - (∑ j ∈ Finset.range m, resetPrice A j)) + _
      rw [Finset.sum_range_succ]; abel
    simpa only [zero_add] using (ih.add ht).congr (fun m => (he m).symm)

end YM.Integration.FVA1Physical.Wilson
