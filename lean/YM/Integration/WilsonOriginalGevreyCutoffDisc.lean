import YM.Integration.WilsonOriginalPhysicalDiscJets
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! The real one-sided Gevrey cutoff used to localize the physical box.
All constants below are independent of the heat and derivative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGevreyCutoffDisc
open Set Filter Metric Complex
open scoped Topology
def leaf (x : ℝ) : ℂ := (expNegInvGlue x:ℂ)
def analytic (z : ℂ) : ℂ := Complex.exp (-z⁻¹)

theorem original {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ‖iteratedDeriv k leaf x‖ ≤ 16^k*(k.factorial:ℝ)^2 := by
  have half : 0 < x/2 := half_pos hx
  have realPart (z : ℂ) (hz : z ∈ closedBall (x:ℂ) (x/2)) : x/2 ≤ z.re := by
    have a := Complex.re_le_norm ((x:ℂ)-z)
    rw [← dist_eq_norm,dist_comm] at a
    have t := a.trans (mem_closedBall.mp hz)
    simp only [Complex.sub_re,Complex.ofReal_re] at t
    linarith
  have nonzero (z : ℂ) (hz : z ∈ closedBall (x:ℂ) (x/2)) : z ≠ 0 := by
    intro eq
    have h := realPart z hz
    simp [eq] at h
    linarith
  have diff : DifferentiableOn ℂ analytic (closedBall (x:ℂ) (x/2)) := by
    intro z hz
    exact (Complex.differentiableAt_exp.comp z (differentiableAt_inv (nonzero z hz)).neg).differentiableWithinAt
  have strip : DiffContOnCl ℂ analytic (ball (x:ℂ) (x/2)) :=
    ⟨diff.mono ball_subset_closedBall,diff.continuousOn.mono closure_ball_subset_closedBall⟩
  have growth (z : ℂ) (hz : z ∈ sphere (x:ℂ) (x/2)) :
      ‖analytic z‖ ≤ Real.exp (-(8*x)⁻¹) := by
    have h := sphere_subset_closedBall hz
    have re := realPart z h
    have normPrice := (norm_le_of_mem_closedBall h)
    have zr : ‖z‖ ≤ 3*x/2 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx] at normPrice
      linarith
    have sq : Complex.normSq z ≤ (3*x/2)^2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) zr 2
    have pp : 0 < Complex.normSq z := Complex.normSq_pos.mpr (nonzero z h)
    rw [analytic,Complex.norm_exp,Complex.neg_re,Complex.inv_re]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [le_div_iff₀ pp,inv_mul_eq_div,div_le_iff₀ (by positivity : 0 < 8*x)]
    nlinarith [mul_le_mul_of_nonneg_right re (by positivity : 0 ≤ 8*x)]
  have same : leaf =ᶠ[𝓝 x] fun t : ℝ => analytic t := by
    filter_upwards [lt_mem_nhds hx] with t ht
    simp [leaf,analytic,expNegInvGlue,ht.not_ge,← Complex.ofReal_inv,← Complex.ofReal_neg,← Complex.ofReal_exp]
  have income := WilsonOriginalPhysicalDiscJets.original analytic leaf x (x/2) _ half same strip growth k
  have y : 0 ≤ (8*x)⁻¹ := by positivity
  have expPay := (div_le_iff₀ (by positivity : 0 < (k.factorial:ℝ))).mp
    (Real.pow_div_factorial_le_exp ((8*x)⁻¹) y k)
  have cancel : ((8*x)⁻¹)^k*Real.exp (-(8*x)⁻¹) ≤ (k.factorial:ℝ) := by
    rw [Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
    exact expPay.trans_eq (mul_comm _ _)
  apply income.trans
  rw [div_le_iff₀ (pow_pos half _)]
  have span : (16:ℝ)^k * (x/2)^k * ((8*x)⁻¹)^k = 1 := by
    rw [← mul_pow,← mul_pow]
    have h : 16 * (x/2) * (8*x)⁻¹ = 1 := by field_simp; ring
    rw [h,one_pow]
  calc
    _ = (16^k*(x/2)^k)*(((8*x)⁻¹)^k*Real.exp (-(8*x)⁻¹))*(k.factorial:ℝ) := by
      rw [← mul_assoc _ _ (Real.exp _),span,one_mul,mul_comm]
    _ ≤ (16^k*(x/2)^k)*(k.factorial:ℝ)*(k.factorial:ℝ) := by gcongr
    _ = _ := by ring

end YM.Integration.WilsonOriginalGevreyCutoffDisc
