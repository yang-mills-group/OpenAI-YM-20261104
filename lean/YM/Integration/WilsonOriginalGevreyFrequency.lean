import YM.Integration.WilsonOriginalIntegerModeCut

/-! Optimize the authentic compact Gevrey-two integration-by-parts
estimate, with tube width proportional to the square of the heater. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGevreyFrequency
open scoped BigOperators

/-- F is the square root of the largest absolute frequency. The derivative
order is chosen after F and u; the three salaries precede both. -/
theorem original (u F A B D : ℝ) (hu : 0 < u) (hF : 0 ≤ F) (hA : 0 ≤ A) (hB : 0 < B)
    (y : ℂ) (tested : ∀ n : ℕ, ‖y‖ * F^(2*n) ≤
      A*(u⁻¹)^2 * Real.exp (D*(u⁻¹)^4) * ((B/u)^(2*n)*(n.factorial:ℝ)^2)) :
    ‖y‖ ≤ (2*A)*(u⁻¹)^2*Real.exp (D*(u⁻¹)^4-(Real.log 2/(2*B))*F*u) := by
  let spend := A*(u⁻¹)^2*Real.exp (D*(u⁻¹)^4)
  have hs : 0 ≤ spend := by dsimp [spend];positivity
  by_cases hzero : F=0
  · subst F
    have base := tested 0
    simp only [Nat.mul_zero,pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,one_pow] at base
    simpa only [mul_zero,zero_mul,sub_zero] using
      (show ‖y‖ ≤ (2*A)*(u⁻¹)^2*Real.exp (D*(u⁻¹)^4) by
        calc
          _ ≤ spend := base
          _ ≤ _ := by dsimp [spend];gcongr;linarith)
  have hFp : 0 < F := lt_of_le_of_ne hF (Ne.symm hzero)
  let z := F*u/(2*B)
  let n := ⌊z⌋₊
  have hz : 0 ≤ z := by dsimp [z];positivity
  have hn : (n:ℝ) ≤ z := Nat.floor_le hz
  have nlimit : (B/u)*(n:ℝ) ≤ F/2 := calc
    _ ≤ (B/u)*z := mul_le_mul_of_nonneg_left hn (div_nonneg hB.le hu.le)
    _ = _ := by dsimp [z];field_simp
  have factorial : (n.factorial:ℝ) ≤ (n:ℝ)^n := by exact_mod_cast n.factorial_le_pow
  have power : (B/u)^(2*n)*(n.factorial:ℝ)^2 ≤ (F/2)^(2*n) := calc
    _ ≤ (B/u)^(2*n)*((n:ℝ)^n)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) factorial 2) (by positivity)
    _ = ((B/u)*(n:ℝ))^(2*n) := by rw [mul_pow,← pow_mul,Nat.mul_comm n 2]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) nlimit _
  have read : ‖y‖ * F^(2*n) ≤ spend*((1/2:ℝ)^(2*n))*F^(2*n) := calc
    _ ≤ spend*((B/u)^(2*n)*(n.factorial:ℝ)^2) := tested n
    _ ≤ spend*(F/2)^(2*n) := mul_le_mul_of_nonneg_left power hs
    _ = _ := by rw [div_pow,one_div,inv_pow];ring
  have fee : ‖y‖ ≤ spend*(1/2:ℝ)^n := by
    apply (le_of_mul_le_mul_right read (pow_pos hFp _)).trans
    apply mul_le_mul_of_nonneg_left _ hs
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have nbelow : z-1 ≤ (n:ℝ) := by
    have := Nat.lt_floor_add_one z
    dsimp only [n];linarith
  have logPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have priced : (1/2:ℝ)^n ≤ 2*Real.exp (-(Real.log 2)*z) := calc
    _ = Real.exp ((n:ℝ)*(-Real.log 2)) := by rw [Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),one_div]
    _ ≤ Real.exp (Real.log 2-Real.log 2*z) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left nbelow logPos.le])
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),neg_mul]
  calc
    _ ≤ spend*(2*Real.exp (-(Real.log 2)*z)) := fee.trans (mul_le_mul_of_nonneg_left priced hs)
    _ = (2*A)*(u⁻¹)^2*(Real.exp (D*(u⁻¹)^4)*Real.exp (-(Real.log 2)*z)) := by dsimp [spend];ring
    _ = _ := by rw [← Real.exp_add];congr 2;dsimp [z];ring

end YM.Integration.WilsonOriginalGevreyFrequency

