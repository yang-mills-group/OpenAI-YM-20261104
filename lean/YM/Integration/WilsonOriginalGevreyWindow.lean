import YM.Integration.WilsonOriginalGevreyCutoffDisc
import Mathlib.Data.Nat.Choose.Cast

/-! The separated physical box has a compact, strictly positive window whose
actual derivatives have one common Gevrey bound for every order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGevreyWindow
open Set Filter Finset
open scoped Topology
open WilsonOriginalGevreyCutoffDisc (leaf)

def window (a b : ℝ) (x : ℝ) : ℂ := leaf (x-a)*leaf (b-x)

theorem smooth {k : ℕ∞} : ContDiff ℝ k leaf :=
  Complex.ofRealCLM.contDiff.comp expNegInvGlue.contDiff

theorem leaf_price (x : ℝ) (n : ℕ) :
    ‖iteratedDeriv n leaf x‖ ≤ 16^n*(n.factorial:ℝ)^2 := by
  by_cases pos : 0 < x
  · exact WilsonOriginalGevreyCutoffDisc.original pos n
  have neg : Iio (0:ℝ) ⊆ {y : ℝ | iteratedDeriv n leaf y = 0} := by
    intro y hy
    have zero : leaf =ᶠ[𝓝 y] fun _ => (0:ℂ) := by
      filter_upwards [gt_mem_nhds (mem_Iio.mp hy)] with t ht
      simp [WilsonOriginalGevreyCutoffDisc.leaf,expNegInvGlue.zero_of_nonpos ht.le]
    change iteratedDeriv n leaf y = 0
    rw [zero.iteratedDeriv_eq n]
    cases n <;> simp
  have closed : IsClosed {y : ℝ | iteratedDeriv n leaf y = 0} :=
    isClosed_eq (ContDiff.continuous_iteratedDeriv' n smooth) continuous_const
  have all := closure_minimal neg closed
  rw [closure_Iio] at all
  rw [show iteratedDeriv n leaf x = 0 from all (not_lt.mp pos),norm_zero]
  positivity

theorem original (a b x : ℝ) (n : ℕ) :
    ‖iteratedDeriv n (window a b) x‖ ≤ 32^n*(n.factorial:ℝ)^2 := by
  let f := fun t : ℝ => leaf (t-a)
  let g := fun t : ℝ => leaf (b-t)
  have hf : ContDiff ℝ n f := smooth.comp (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ n g := smooth.comp (contDiff_const.sub contDiff_id)
  let fee := 16^n*(n.factorial:ℝ)^2
  have pos : 0 ≤ fee := by positivity
  have single (i : ℕ) (hi : i ≤ n) :
      ‖(n.choose i:ℂ)*iteratedDeriv i f x*iteratedDeriv (n-i) g x‖ ≤ fee := by
    have fac : (n.choose i:ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ) = (n.factorial:ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have one : (1:ℝ) ≤ n.choose i := by exact_mod_cast Nat.choose_pos hi
    have joint : (i.factorial:ℝ)*((n-i).factorial:ℝ) ≤ n.factorial := by
      rw [← fac,mul_assoc]
      exact le_mul_of_one_le_left (by positivity) one
    have pay : (16:ℝ)^i*16^(n-i) = 16^n := by rw [← pow_add,Nat.add_sub_of_le hi]
    simp only [norm_mul,Complex.norm_natCast,f,g,iteratedDeriv_comp_sub_const,
      iteratedDeriv_comp_const_sub,norm_smul,norm_pow,Real.norm_eq_abs,abs_neg,abs_one,one_pow,one_mul]
    calc
      _ ≤ (n.choose i:ℝ)*(16^i*(i.factorial:ℝ)^2)*(16^(n-i)*((n-i).factorial:ℝ)^2) := by
        gcongr <;> apply leaf_price
      _ = (16^i*16^(n-i))*((n.choose i:ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ))*
          ((i.factorial:ℝ)*((n-i).factorial:ℝ)) := by ring
      _ ≤ (16^n*(n.factorial:ℝ))*(n.factorial:ℝ) := by
        rw [pay,fac]
        exact mul_le_mul_of_nonneg_left joint (by positivity)
      _ = fee := by dsimp [fee];ring
  change ‖iteratedDeriv n (f*g) x‖ ≤ _
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  calc
    _ ≤ ∑ i ∈ range (n+1), ‖(n.choose i:ℂ)*iteratedDeriv i f x*iteratedDeriv (n-i) g x‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ range (n+1), fee := sum_le_sum fun i hi => single i (by have := mem_range.mp hi;omega)
    _ = (n+1:ℕ)*fee := by simp
    _ ≤ (2:ℝ)^n*fee := mul_le_mul_of_nonneg_right (by exact_mod_cast n.lt_two_pow_self) pos
    _ = _ := by dsimp [fee]; rw [← mul_assoc,← mul_pow];norm_num

end YM.Integration.WilsonOriginalGevreyWindow
