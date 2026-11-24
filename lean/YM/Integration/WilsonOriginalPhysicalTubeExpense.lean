import YM.Integration.WilsonOriginalGevreyDiscProduct

/-! Use the radius and size appointed at the initial reader election. The
Gevrey constant is fixed across radii and across every derivative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalTubeExpense
open Filter Metric
open scoped Topology ContDiff
def B (H c : ℝ) := Real.sqrt (2*max H c⁻¹)

theorem original {F : ℂ → ℂ} {f χ : ℝ → ℂ} (x u w c D C H : ℝ) (hu : 0 < u)
    (small : u ≤ 1) (hc : 0 < c) (paidWidth : c*u^2 ≤ w) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (n : ℕ) (continues : f =ᶠ[𝓝 x] fun y : ℝ => F y)
    (holomorphic : DiffContOnCl ℂ F (ball (x:ℂ) w))
    (growth : ∀ z ∈ sphere (x:ℂ) w, ‖F z‖ ≤ Real.exp (D*u⁻¹^4))
    (sχ : ContDiffAt ℝ n χ x) (sf : ContDiffAt ℝ n f x)
    (cutoff : ∀ i ≤ n, ‖iteratedDeriv i χ x‖ ≤ C*H^i*(i.factorial:ℝ)^2) :
    0 < B H c ∧ ‖iteratedDeriv n (χ*f) x‖ ≤
      C*(u⁻¹)^2*Real.exp (D*u⁻¹^4)*((B H c/u)^(2*n)*(n.factorial:ℝ)^2) := by
  have hw : 0 < w := (mul_pos hc (pow_pos hu 2)).trans_le paidWidth
  have hm : 0 < max H c⁻¹ := (inv_pos.mpr hc).trans_le (le_max_right _ _)
  have hB : 0 < B H c := Real.sqrt_pos.2 (mul_pos (by norm_num) hm)
  refine ⟨hB,?_⟩
  have invPrice : w⁻¹*u^2 ≤ c⁻¹ := by
    rw [← div_eq_inv_mul,div_le_iff₀ hw]
    have cost := mul_le_mul_of_nonneg_left paidWidth (inv_pos.mpr hc).le
    simpa only [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using cost
  have strip : (max H w⁻¹)*u^2 ≤ max H c⁻¹ := by
    by_cases h : H ≤ w⁻¹
    · rw [max_eq_right h];exact invPrice.trans (le_max_right _ _)
    · rw [max_eq_left (le_of_not_ge h)]
      exact (mul_le_of_le_one_right hH (pow_le_one₀ hu.le small)).trans (le_max_left _ _)
  have factor : 2*max H w⁻¹ ≤ (B H c/u)^2 := by
    rw [div_pow,B,Real.sq_sqrt (by positivity),le_div_iff₀ (pow_pos hu 2),mul_assoc]
    exact mul_le_mul_of_nonneg_left strip (by norm_num)
  have cost := WilsonOriginalGevreyDiscProduct.original x w (Real.exp (D*u⁻¹^4)) C H hw
    (Real.exp_pos _).le hC hH n continues holomorphic growth sχ sf cutoff
  have power := pow_le_pow_left₀ (mul_nonneg zero_le_two ((inv_pos.mpr hw).le.trans (le_max_right _ _))) factor n
  have up : 1 ≤ (u⁻¹)^2 := one_le_pow₀ ((one_le_inv₀ hu).mpr small)
  apply cost.trans
  calc
    _ ≤ C*Real.exp (D*u⁻¹^4)*(((B H c/u)^2)^n)*(n.factorial:ℝ)^2 := by gcongr
    _ ≤ C*(u⁻¹)^2*Real.exp (D*u⁻¹^4)*(((B H c/u)^2)^n)*(n.factorial:ℝ)^2 := by
      gcongr
      exact le_mul_of_one_le_right hC up
    _ = _ := by rw [pow_mul];ring

end YM.Integration.WilsonOriginalPhysicalTubeExpense

