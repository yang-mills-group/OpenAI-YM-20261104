import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralFieldCutoff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedBilateralBumpWages
open Finset Filter Set
open scoped Topology ContDiff BigOperators Classical
def bump (x : ℝ) : ℝ := Real.smoothTransition (2+x) * Real.smoothTransition (2-x)
def profile (n : ℕ) (x : ℝ) : ℝ := bump x * x^n
theorem smooth : ContDiff ℝ ∞ bump := by unfold bump; fun_prop
theorem outside {x : ℝ} (hx : 2 ≤ |x|) : bump x = 0 := by
  unfold bump
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx),mul_zero]
  · rw [abs_of_neg (lt_of_not_ge h)] at hx
    rw [Real.smoothTransition.zero_of_nonpos (show 2+x ≤ 0 by linarith),zero_mul]
private theorem powers {j k n : ℕ} (hj : j ≤ k) {x : ℝ} (hx : |x| ≤ 2) :
    ‖iteratedDeriv j (fun t : ℝ => t^n) x‖ ≤ (n+1:ℝ)^k * 2^n := by
  have hc : (n.descFactorial j : ℝ) ≤ (n+1:ℝ)^k := by
    exact_mod_cast (Nat.descFactorial_le_pow n j).trans
      ((Nat.pow_le_pow_left (Nat.le_succ n) j).trans (Nat.pow_le_pow_right (Nat.succ_pos n) hj))
  rw [iteratedDeriv_pow,norm_mul,Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ n.descFactorial j),norm_pow,Real.norm_eq_abs]
  apply mul_le_mul hc _ (by positivity) (by positivity)
  exact (pow_le_pow_left₀ (abs_nonneg x) hx _).trans
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.sub_le _ _))

theorem original (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x : ℝ,
    ‖iteratedDeriv k (profile n) x‖ ≤ C*((n+1:ℝ)^k*2^n) := by
  have bounds (j : ℕ) : ∃ c : ℝ, ∀ x ∈ Icc (-2:ℝ) 2, ‖iteratedDeriv j bump x‖ ≤ c :=
    isCompact_Icc.exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedDeriv j smooth (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).continuousOn
  choose c hc using bounds
  let C := ∑ j ∈ range (k+1), (k.choose j : ℝ) * max (c j) 0
  have nonneg : 0 ≤ C := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right ..)
  refine ⟨C,nonneg,fun n x => ?_⟩
  by_cases hx : |x| ≤ 2
  · change ‖iteratedDeriv k (bump * fun t : ℝ => t^n) x‖ ≤ _
    have hp : ContDiff ℝ (k : ℕ∞ω) (fun t : ℝ => t^n) := by fun_prop
    have hb : ContDiff ℝ (k : ℕ∞ω) bump := smooth.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
    rw [iteratedDeriv_mul (x:=x) hb.contDiffAt hp.contDiffAt]
    apply (norm_sum_le _ _).trans
    rw [show C*((n+1:ℝ)^k*2^n) = ∑ j ∈ range (k+1),
      ((k.choose j : ℝ) * max (c j) 0)*((n+1:ℝ)^k*2^n) from by dsimp only [C]; rw [Finset.sum_mul]]
    apply Finset.sum_le_sum
    intro j _
    simp only [norm_mul,Real.norm_natCast]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ((hc j x (abs_le.mp hx)).trans (le_max_left ..)) (Nat.cast_nonneg _))
      (powers (Nat.sub_le k j) hx) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (le_max_right ..))
  · have vanish : profile n =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(continuous_abs.tendsto x).eventually (eventually_gt_nhds (lt_of_not_ge hx))] with y hy
      simp only [profile,outside hy.le,zero_mul]
    rw [vanish.iteratedDeriv_eq k]
    simpa using mul_nonneg nonneg (by positivity : 0 ≤ (n+1:ℝ)^k*2^n)
end IssuedBridge.PostedBilateralBumpWages
