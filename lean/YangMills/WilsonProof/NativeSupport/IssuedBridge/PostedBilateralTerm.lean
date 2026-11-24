import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralWidth
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralBumpWages
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedBilateralTerm
open Filter Set Finset PostedBilateralWidth PostedBilateralBumpWages
open scoped Topology ContDiff BigOperators Classical
variable {E : ℕ → Type*} [∀ d, NormedAddCommGroup (E d)] [∀ d, NormedSpace ℝ (E d)]
variable (a : ∀ d, ℕ → E d)

theorem rescale (n : ℕ) : PostedBilateralFieldCutoff.weight a n =
    fun t => ((width a n)^n)⁻¹ * profile n (width a n*t) := by
  funext t
  have hw : width a n ≠ 0 := by linarith [PostedBilateralWidth.floor a n]
  change Real.smoothTransition (2+width a n*t) *
    (Real.smoothTransition (2-width a n*t) * t^n) = _
  dsimp only [profile,bump]
  rw [mul_pow]
  field_simp

theorem original (n k d : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (fun y => PostedBilateralFieldCutoff.weight a n y • a d n) t‖ =
      ((width a n)^n)⁻¹ * (width a n)^k * ‖iteratedDeriv k (profile n) (width a n*t)‖ * ‖a d n‖ := by
  have hk : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have hp : ContDiff ℝ (k : ℕ∞ω) (profile n) := by unfold profile bump; fun_prop
  have hw : 0 ≤ width a n := by linarith [PostedBilateralWidth.floor a n]
  rw [iteratedDeriv_smul_const ((PostedBilateralFieldCutoff.original a n).1.of_le hk).contDiffAt,
    rescale,iteratedDeriv_const_mul_field,iteratedDeriv_comp_const_mul hp,norm_smul,norm_mul,norm_mul]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hw n)),Real.norm_of_nonneg (pow_nonneg hw k)]
  ring
end IssuedBridge.PostedBilateralTerm
