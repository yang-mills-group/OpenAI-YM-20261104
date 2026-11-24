import YM.Integration.WilsonReportingAbsoluteInletForecastBooks
import YM.Integration.WilsonOlderFreshSoftSocketKinetic

/-! Truncation of real series at the finite coupling used by an original clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticTruncation
open Finset PowerSeries WilsonCoeffUV.Blue WilsonReportingAbsoluteInletForecastBooks
open private convolution multiply from YM.Integration.WilsonReportingAbsoluteInletForecastBooks
open scoped BigOperators Classical

private def major (A:Cost):Cost:=PowerSeries.mk fun i=>|coeff i A|

private theorem major_mul (i:ℕ)(A B:Cost):|coeff i (A*B)| ≤ coeff i (major A*major B):=by
  rw [coeff_mul,coeff_mul];apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum;intro j _;simp [major,abs_mul]

theorem mass_nonneg (n:ℕ)(A:Cost):0 ≤ mass n A:=sum_nonneg fun _ _=>abs_nonneg _

theorem mass_mul (n:ℕ)(A B:Cost):mass n (A*B) ≤ mass n A*mass n B:=by
  calc
    _ ≤ value n (major A*major B) 1:=by
      unfold mass value;apply sum_le_sum;intro i _;simp only [one_pow,one_mul];apply major_mul
    _ ≤ mass n A*mass n B:=by
      rw [convolution];unfold mass;rw [sum_mul];apply sum_le_sum;intro i _;rw [mul_sum]
      apply sum_le_sum;intro j _;split_ifs
      · simp [major]
      · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem one_value (n:ℕ)(x:ℝ):value n 1 x=1:=by simp [value,coeff_one]

theorem head (n:ℕ):mass n 1=1:=by simp [mass,coeff_one,abs_ite]

theorem mass_pow (n s:ℕ)(A:Cost):mass n (A^s) ≤ (mass n A)^s:=by
  induction s with
  | zero=>simp [head]
  | succ s ih=>rw [pow_succ,pow_succ];exact (mass_mul ..).trans (mul_le_mul_of_nonneg_right ih (mass_nonneg ..))

theorem norm (n:ℕ)(A:Cost){x:ℝ}(x0:0 ≤ x)(x1:x ≤ 1):|value n A x| ≤ mass n A:=by
  apply (abs_sum_le_sum_abs ..).trans;apply sum_le_sum;intro i _
  rw [abs_mul,abs_of_nonneg (pow_nonneg x0 _)]; exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ x0 x1)

theorem tail {t n:ℕ}(tn:t ≤ n)(A:Cost){x:ℝ}(x0:0 ≤ x)(x1:x ≤ 1):
    |value n A x-value t A x| ≤ x^(t+1)*mass n A:=by
  unfold value mass
  rw [←Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ tn),mul_sum]
  refine (abs_sum_le_sum_abs ..).trans ?_
  refine (sum_le_sum (g:=fun i=>x^(t+1)*|coeff i A|) fun i hi=>?_).trans ?_
  · rw [abs_mul,abs_of_nonneg (pow_nonneg x0 _)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one x0 x1 (mem_Ico.mp hi).1) (abs_nonneg _)
  · apply sum_le_sum_of_subset_of_nonneg (fun i hi=>mem_range.mpr (mem_Ico.mp hi).2)
    intro _ _ _;positivity

theorem powers (n s:ℕ)(A:Cost){x:ℝ}(x0:0 ≤ x)(x1:x ≤ 1):
    |value n (A^s) x-(value n A x)^s| ≤ s*x^(n+1)*(mass n A)^s:=by
  induction s with
  | zero=>simp [one_value]
  | succ s ih=>
    let M:=mass n A
    have M0:0 ≤ M:=mass_nonneg ..
    have ev:=norm n A x0 x1
    have prod:=multiply n x x0 x1 (A^s) A
    rw [pow_succ,pow_succ (value n A x)]
    calc
      _ ≤ |value n (A^s*A) x-value n (A^s) x*value n A x|+
          |value n (A^s) x*value n A x-(value n A x)^s*value n A x|:=abs_sub_le ..
      _ ≤ x^(n+1)*((M^s)*M)+(s*x^(n+1)*M^s)*M:=by
        apply add_le_add
        · exact prod.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mass_pow ..) M0) (pow_nonneg x0 _))
        · rw [←sub_mul,abs_mul];exact mul_le_mul ih ev (abs_nonneg _) (by positivity)
      _=_:=by change _=((s+1:ℕ):ℝ)*x^(n+1)*M^(s+1);rw [Nat.cast_succ,pow_succ];ring

theorem short_power {t n:ℕ}(tn:t ≤ n)(s:ℕ)(A:Cost){x:ℝ}(x0:0 ≤ x)(x1:x ≤ 1):
    |value t (A^s) x-(value n A x)^s| ≤ (s+1:ℝ)*x^(t+1)*(mass n A)^s:=by
  calc
    _ ≤ |value t (A^s) x-value n (A^s) x|+|value n (A^s) x-(value n A x)^s|:=abs_sub_le ..
    _ ≤ x^(t+1)*(mass n A)^s+(s:ℝ)*x^(t+1)*(mass n A)^s:=by
      apply add_le_add
      · rw [abs_sub_comm];exact (tail tn _ x0 x1).trans (mul_le_mul_of_nonneg_left (mass_pow ..) (pow_nonneg x0 _))
      · refine (powers n s A x0 x1).trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one x0 x1 (Nat.succ_le_succ tn)) (Nat.cast_nonneg _)) (pow_nonneg (mass_nonneg ..) _)
    _=_:=by ring

end YM.Integration.WilsonSeparatedPrefixKineticTruncation
end
