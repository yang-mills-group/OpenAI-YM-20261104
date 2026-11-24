import YM.Integration.WilsonOriginalOccupiedSalary

/-! A summable senior-date tariff for each original withdrawal in the optical window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedDateShare
open Finset Filter
open scoped BigOperators Classical

def weight (l:ℕ):ℝ:=(l+1:ℝ)*(l+2:ℝ)

theorem hot {x C:ℝ} (d l:ℕ)(xp:1 ≤ x)(cp:0 ≤ C)(high:C*2^d+2 ≤ x)
    (span:(l:ℝ) ≤ C*(1+Real.log x)^d):weight l ≤ x^(2*(d+1)):=by
  have x0:0 ≤ x:=zero_le_one.trans xp
  have low:0 ≤ 1+Real.log x:=by linarith only [Real.log_nonneg xp]
  have clock:1+Real.log x ≤ 2*x:=by linarith only [xp,Real.log_le_self x0]
  have toll:(l:ℝ) ≤ C*(2*x)^d:=span.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ low clock _) cp)
  rw [mul_pow] at toll
  have d1:1 ≤ x^d:=one_le_pow₀ xp
  have large:(l:ℝ)+2 ≤ x^(d+1):=by
    calc _ ≤ (C*2^d+2)*x^d:=by nlinarith only [toll,d1]
         _ ≤ _:=by rw [pow_succ];exact (mul_le_mul_of_nonneg_right high (pow_nonneg x0 _)).trans_eq (mul_comm ..)
  unfold weight
  rw [two_mul,pow_add]
  exact mul_le_mul ((by linarith:(l:ℝ)+1≤(l:ℝ)+2).trans large) large (by positivity) (pow_nonneg x0 _)

theorem total (M:ℕ):∑l∈range M,1/weight l=1-1/(M+1:ℝ):=by
  induction M with
  | zero=>norm_num
  | succ M ih=>
    rw [sum_range_succ,ih];unfold weight;push_cast
    have p:0<(M:ℝ)+1:=by positivity
    have p':0<(M:ℝ)+2:=by positivity
    have p'':(M:ℝ)+1+1=(M:ℝ)+2:=by ring
    rw [p''];field_simp;ring

end YM.Integration.WilsonOriginalOccupiedDateShare
