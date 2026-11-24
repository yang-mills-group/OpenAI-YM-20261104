import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-! The original Fourier test is a product of a fixed compact cutoff and
a unit-modulus exponential. Its derivative loss is fixed before the heat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalModulatedProfiles
open Complex Finset
open scoped BigOperators ContDiff
def wave (c : ℂ) (x : ℝ) := Complex.exp (c*(x:ℂ))

theorem derivative (c : ℂ) (n : ℕ) : iteratedDeriv n (wave c) =
    fun x : ℝ => c^n*wave c x := by
  induction n with
  | zero => ext;simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have one := (((Complex.hasDerivAt_exp (c*(x:ℂ))).comp (x:ℂ)
      ((hasDerivAt_id (x:ℂ)).const_mul c)).comp_ofReal).const_mul (c^n)
    convert one.deriv using 1 <;> simp [wave,pow_succ]
    ring

theorem original (χ : ℝ → ℂ) (c : ℂ) (x : ℝ) (n : ℕ) (H : ℝ)
    (smooth : ContDiffAt ℝ n χ x) (hH : 0 ≤ H) (low : ∀ i ≤ n, ‖iteratedDeriv i χ x‖ ≤ H)
    (pure : c.re = 0) : ‖iteratedDeriv n (χ*wave c) x‖ ≤
      ((2:ℝ)^n*H)*(1+‖c‖)^n := by
  have modOne : ‖wave c x‖ = 1 := by simp [wave,Complex.norm_exp,Complex.mul_re,pure]
  have smoothWave : ContDiffAt ℝ n (wave c) x := by
    have cast : ContDiffAt ℝ n (fun x : ℝ => (x:ℂ)) x := Complex.ofRealCLM.contDiff.contDiffAt
    exact (contDiffAt_const.mul cast).cexp
  rw [iteratedDeriv_mul smooth smoothWave]
  calc
    _ ≤ ∑ i ∈ range (n+1), ‖(n.choose i:ℂ)*iteratedDeriv i χ x*iteratedDeriv (n-i) (wave c) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ range (n+1), (n.choose i:ℝ)*H*(1+‖c‖)^n := by
      apply sum_le_sum
      intro i hi
      simp only [derivative,norm_mul,norm_pow,modOne,mul_one,Complex.norm_natCast]
      have a := low i (by have := mem_range.mp hi;omega)
      have g : ‖c‖^(n-i) ≤ (1+‖c‖)^n := calc
        _ ≤ (1+‖c‖)^(n-i) := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ _ := pow_le_pow_right₀ (by linarith [norm_nonneg c]) (Nat.sub_le _ _)
      gcongr
    _ = _ := by rw [← sum_mul,← sum_mul,← Nat.cast_sum,Nat.sum_range_choose];norm_cast

end YM.Integration.WilsonOriginalModulatedProfiles

