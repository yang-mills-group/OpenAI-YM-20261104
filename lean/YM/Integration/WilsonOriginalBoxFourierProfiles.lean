import YM.Integration.WilsonOriginalModulatedProfiles
import YM.Integration.WilsonOriginalFourierLattice

/-! The tensor product of the actual normalized torus characters times
the filed compact cutoffs costs a fixed spatial seminorm before every crop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBoxFourierProfiles
open Finset Complex
open scoped BigOperators ContDiff
open WilsonOriginalFourierLattice (height)
open WilsonOriginalModulatedProfiles (wave)
def frequency (k : ℤ) : ℂ := -2*(Real.pi:ℂ)*Complex.I*(k:ℂ)

/-- Each coordinate may use its own compact cutoff and derivative order. -/
theorem original {d : ℕ} (χ : Fin d → ℝ → ℂ) (rents : Fin d → ℝ) (v : Fin d → ℤ)
    (x : Fin d → ℝ) (orders : Fin d → ℕ)
    (smooth : ∀ i, ContDiffAt ℝ (orders i) (χ i) (x i))
    (nonneg : ∀ i, 0 ≤ rents i)
    (bounds : ∀ i k, k ≤ orders i → ‖iteratedDeriv k (χ i) (x i)‖ ≤ rents i) :
    ‖∏ i, iteratedDeriv (orders i) (χ i*wave (frequency (v i))) (x i)‖ ≤
      (∏ i, ((2:ℝ)^(orders i)*rents i)*(1+2*Real.pi)^(orders i)) *
        (1+(height v:ℝ))^(∑ i,orders i) := by
  have own (i : Fin d) : ‖iteratedDeriv (orders i) (χ i*wave (frequency (v i))) (x i)‖ ≤
      (((2:ℝ)^orders i*rents i)*(1+2*Real.pi)^orders i)*(1+(height v:ℝ))^orders i := by
    have re : (frequency (v i)).re = 0 := by simp [frequency,Complex.mul_re,Complex.mul_im]
    have price := WilsonOriginalModulatedProfiles.original (χ i) (frequency (v i)) (x i) (orders i)
      (rents i) (smooth i) (nonneg i) (bounds i) re
    have single : ((v i).natAbs:ℝ) ≤ (height v:ℝ) := by
      exact_mod_cast Finset.le_sup (f:=fun k => (v k).natAbs) (mem_univ i)
    have rate : 1+‖frequency (v i)‖ ≤ (1+2*Real.pi)*(1+(height v:ℝ)) := by
      have abs : ‖((v i:ℤ):ℂ)‖ = ((v i).natAbs:ℝ) := by simp
      simp only [frequency,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos Real.pi_pos,Complex.norm_I,mul_one,abs]
      nlinarith [Nat.cast_nonneg (α:=ℝ) (height v),Real.pi_pos,
        mul_le_mul_of_nonneg_left single Real.pi_pos.le]
    calc
      _ ≤ _ := price
      _ ≤ ((2:ℝ)^orders i*rents i)*(((1+2*Real.pi)*(1+(height v:ℝ)))^orders i) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) rate _)
          (mul_nonneg (by positivity) (nonneg i))
      _ = _ := by rw [mul_pow];ring
  rw [norm_prod,← Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => own i)
    _ = _ := Finset.prod_mul_distrib

end YM.Integration.WilsonOriginalBoxFourierProfiles

