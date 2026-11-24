import YM.LocalLTE.Units.Vain
import YM.Integration.FVA1Physical.Round2.FieldSharpClock

/-! Uniform interpolation in the real regular chart. Buying sufficiently
high comparison order pays for the derivatives lost by finite differences.
The interpolation constant depends only on the two derivative orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Metric LocalLTE.Cabana PhysicalNext.Repeat ConnectedActivityE6.Blaze
open scoped Topology ContDiff

theorem field_derivative_reserve (k j : ℕ) (hj : j<k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E→ℝ) (x : E) (a b p : ℕ) (g : ℝ), 0<g → g≤1 → b+(p+a*j)≤a*k →
      (∀ y : E, ‖y‖≤g^a → ContDiffAt ℝ k f (y+x) ∧
        ‖iteratedFDeriv ℝ k f (y+x)‖ ≤ (g⁻¹)^b ∧ |f (y+x)| ≤ g^(p+a*j)) →
      ‖iteratedFDeriv ℝ j f x‖ ≤ C*g^p := by
  obtain ⟨K,hK,use⟩:=resurrect k j hj
  refine ⟨2*K,mul_nonneg zero_le_two hK,?_⟩
  intro E _ _ f x a b p g hg h1 high paid
  have hr : 0 < g^a := pow_pos hg a
  have balance : (g⁻¹)^b*(g^a)^k ≤ g^(p+a*j) := by
    rw [←pow_mul,inv_pow,inv_mul_le_iff₀ (pow_pos hg b),←pow_add]
    exact pow_le_pow_of_le_one hg.le h1 high
  have brush:=use E f x 0 (g^a) (g^a) ((g⁻¹)^b) (g^(p+a*j)) hr
    (by simp) (pow_nonneg (inv_nonneg.mpr hg.le) _) (pow_nonneg hg.le _) (fun y dart=>by
      obtain ⟨s,hs,inside⟩:=dart
      have hnorm : ‖y‖ ≤ g^a := by
        simpa only [smul_zero,sub_zero] using inside.trans (mul_le_of_le_one_left hr.le hs.2)
      simpa only [Real.norm_eq_abs] using paid y hnorm)
  have orig:=brush.order j le_rfl
  change ‖iteratedFDeriv ℝ j f x‖ ≤ _ at orig
  apply orig.trans
  calc
    _ ≤ K*(2*g^(p+a*j))*(g^a)⁻¹^j := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [balance]) hK) (pow_nonneg (inv_nonneg.mpr hr.le) _)
    _ = 2*K*g^p := by
      rw [pow_add, pow_mul, inv_pow]
      field_simp

end YM.Integration.FVA1Physical.Round2.Curvature
