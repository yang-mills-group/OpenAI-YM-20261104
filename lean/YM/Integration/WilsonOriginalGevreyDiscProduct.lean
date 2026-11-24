import YM.Integration.WilsonOriginalPhysicalDiscJets
import Mathlib.Data.Nat.Choose.Cast

/-! Localized real derivative salary from the genuine complex disc and
the actual one-dimensional Gevrey cutoff on a physical coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGevreyDiscProduct
open Finset Filter Metric
open scoped BigOperators Topology ContDiff
theorem original {F : ℂ → ℂ} {f χ : ℝ → ℂ} (x w M C H : ℝ)
    (hw : 0 < w) (hM : 0 ≤ M) (hC : 0 ≤ C) (hH : 0 ≤ H) (n : ℕ)
    (continues : f =ᶠ[𝓝 x] fun t : ℝ => F t)
    (holomorphic : DiffContOnCl ℂ F (ball (x:ℂ) w))
    (size : ∀ z ∈ sphere (x:ℂ) w, ‖F z‖ ≤ M)
    (sχ : ContDiffAt ℝ n χ x) (sf : ContDiffAt ℝ n f x)
    (cutoff : ∀ i ≤ n, ‖iteratedDeriv i χ x‖ ≤ C*H^i*(i.factorial:ℝ)^2) :
    ‖iteratedDeriv n (χ*f) x‖ ≤ C*M*(2*max H w⁻¹)^n*(n.factorial:ℝ)^2 := by
  let B := max H w⁻¹
  have hB : 0 ≤ B := hH.trans (le_max_left _ _)
  let fee := C*M*B^n*(n.factorial:ℝ)^2
  have hfee : 0 ≤ fee := by dsimp [fee];positivity
  have each (i : ℕ) (hi : i ≤ n) :
      ‖(n.choose i:ℂ)*iteratedDeriv i χ x*iteratedDeriv (n-i) f x‖ ≤ fee := by
    have raw := WilsonOriginalPhysicalDiscJets.original F f x w M hw continues holomorphic size (n-i)
    have cr : ‖iteratedDeriv (n-i) f x‖ ≤ M*(w⁻¹)^(n-i)*((n-i).factorial:ℝ) := by
      simpa only [div_eq_mul_inv,inv_pow] using (show _ ≤ _ from raw) |>.trans_eq (by ring)
    have fac : (n.choose i:ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ) = (n.factorial:ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have ip : (i.factorial:ℝ) ≤ (n.factorial:ℝ) := by exact_mod_cast Nat.factorial_le hi
    have lower := cutoff i hi
    simp only [norm_mul,Complex.norm_natCast]
    calc
      _ ≤ (n.choose i:ℝ)*(C*B^i*(i.factorial:ℝ)^2)*(M*B^(n-i)*((n-i).factorial:ℝ)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (lower.trans ?_) (by positivity)) (cr.trans ?_)
          (norm_nonneg _) (by positivity)
        · gcongr
          exact le_max_left _ _
        · gcongr
          exact le_max_right _ _
      _ = C*M*B^n*((n.choose i:ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ))*(i.factorial:ℝ) := by
        have hp : B^i*B^(n-i)=B^n := by rw [← pow_add,Nat.add_sub_of_le hi]
        calc
          _ = C*M*(B^i*B^(n-i))*((n.choose i:ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ))*(i.factorial:ℝ) := by ring
          _ = _ := by rw [hp]
      _ ≤ fee := by
        rw [fac]
        apply (mul_le_mul_of_nonneg_left ip (show 0 ≤ C*M*B^n*(n.factorial:ℝ) by positivity)).trans_eq
        dsimp only [fee]
        ring
  rw [iteratedDeriv_mul sχ sf]
  calc
    _ ≤ ∑ i ∈ range (n+1), ‖(n.choose i:ℂ)*iteratedDeriv i χ x*iteratedDeriv (n-i) f x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ range (n+1), fee := sum_le_sum fun i hi => each i (by have := mem_range.mp hi;omega)
    _ = (n+1:ℕ)*fee := by simp
    _ ≤ (2:ℝ)^n*fee := mul_le_mul_of_nonneg_right (by exact_mod_cast n.lt_two_pow_self) hfee
    _ = _ := by dsimp [fee,B];rw [mul_pow];ring

end YM.Integration.WilsonOriginalGevreyDiscProduct

