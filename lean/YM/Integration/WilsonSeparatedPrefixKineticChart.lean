import YM.Integration.WilsonSeparatedPrefixKineticTruncation

/-! Finite evaluation of the native composition of kinetic ratios. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticChart
open Finset PowerSeries WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonSeparatedPrefixKineticTruncation WilsonReportingAbsoluteInletForecastBooks
open scoped Classical BigOperators

private theorem triangular (n:ℕ)(f:ℕ→ℕ→ℝ):
    (∑a∈range (n+1),∑i∈range (a+1),f i (a-i))=
      ∑i∈range (n+1),∑j∈range (n-i+1), f i j:=by
  let r:=range (n+1)
  let g(i a j:ℕ):ℝ:=if i+j=a then f i j else 0
  have row (i a:ℕ)(ha:a∈r):(∑j∈r,g i a j)=if i ≤ a then f i (a-i) else 0:=by
    have bound:=mem_range.mp ha
    by_cases h:i ≤ a
    · rw [if_pos h,sum_eq_single_of_mem (a-i) (mem_range.mpr (by omega)),show g i _ _=_ from if_pos (by omega:i+(a-i)=a)]
      exact fun k _ ne=>if_neg (by omega:i+k≠a)
    · rw [if_neg h];exact sum_eq_zero fun j _=>if_neg (by omega:i+j≠a)
  have left (a:ℕ)(ha:a∈r):(∑i∈range (a+1),f i (a-i))=∑i∈r,∑j∈r,g i a j:=by
    simp_rw [row _ _ ha]
    have lim:=mem_range.mp ha
    symm
    rw [←sum_subset (range_mono (by omega : a+1 ≤ n+1))]
    · apply sum_congr rfl;intro i hi;rw [if_pos (mem_range_succ_iff.mp hi)]
    · intro j _ hj;exact if_neg (by simpa [mem_range_succ_iff] using hj)
  have right (i:ℕ)(hi:i∈r):(∑j∈r,∑a∈r,g i a j)=∑j∈range (n-i+1),f i j:=by
    have lim:=mem_range.mp hi
    simp only [g,r,sum_ite_eq,mem_range,Nat.lt_succ_iff]
    rw [←sum_subset (range_mono (by omega : n-i+1 ≤ n+1))]
    · apply sum_congr rfl;intro j hj;rw [if_pos (by have:=mem_range.mp hj;omega)]
    · intro j _ hj;exact if_neg (by have:=not_lt.mp (mt mem_range.mpr hj);omega)
  calc
    _=∑a∈r,∑i∈r,∑j∈r,g i a j:=sum_congr rfl left
    _=∑i∈r,∑j∈r,∑a∈r,g i a j:=by rw [sum_comm];apply sum_congr rfl;intro i _;rw [sum_comm]
    _=_:=sum_congr rfl right

theorem expand (n:ℕ)(A B:Cost)(x:ℝ):value n (chartB A B) x=
    ∑i∈range (n+1),(x^i*coeff i A)*value (n-i) (B^(i+1)) x:=by
  let f(i j:ℕ):ℝ:=x^(i+j)*(coeff i A*coeff j (B^(i+1)))
  calc
    _=∑a∈range (n+1),∑i∈range (a+1),f i (a-i):=by
      unfold value;apply sum_congr rfl;intro a _;rw [chart_coeff,mul_sum]
      apply sum_congr rfl;intro i hi;dsimp [f];rw [Nat.add_sub_of_le (mem_range_succ_iff.mp hi)]
    _=_:= (triangular n f).trans (by
      apply sum_congr rfl;intro i _;unfold value;rw [mul_sum];apply sum_congr rfl;intro j _;dsimp [f];rw [pow_add];ring)

def measured (n:ℕ)(A:Cost)(x r:ℝ):ℝ:=r*value n A (x*r)

private theorem placed (n:ℕ)(A:Cost)(x r:ℝ):measured n A x r=
    ∑i∈range (n+1),(x^i*coeff i A)*r^(i+1):=by
  unfold measured value;rw [mul_sum];apply sum_congr rfl;intro i _;rw [mul_pow,pow_succ];ring

theorem cost (n:ℕ)(A B:Cost){x:ℝ}(x0:0 ≤ x)(x1:x ≤ 1):
    |value n (chartB A B) x-measured n A x (value n B x)|  ≤ 
      x^(n+1)*((n:ℝ)+2)*(max 1 (mass n B))^(n+1)*mass n A:=by
  rw [expand,placed,←sum_sub_distrib];unfold mass;rw [mul_sum]
  apply (abs_sum_le_sum_abs ..).trans;apply sum_le_sum;intro i hi
  have hn:i ≤ n:=mem_range_succ_iff.mp hi
  have hi':(i+1:ℕ) ≤ n+1:=by omega
  have small:=short_power (Nat.sub_le n i) (i+1) B x0 x1
  rw [←mul_sub,abs_mul,abs_mul,abs_of_nonneg (pow_nonneg x0 _)]
  let M:=max 1 (mass n B)
  have cap:(mass n B)^(i+1) ≤ M^(n+1):=(pow_le_pow_left₀ (mass_nonneg ..) (le_max_right ..) _).trans
    (pow_le_pow_right₀ (le_max_left ..) hi')
  have coeffFee:((i+1:ℕ):ℝ)+1 ≤ (n:ℝ)+2:=by push_cast;exact_mod_cast (by omega:i+1+1 ≤ n+2)
  calc
    _ ≤ (x^i*|coeff i A|)*(((n:ℝ)+2)*x^(n-i+1)*M^(n+1)):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity);apply small.trans
      exact mul_le_mul (mul_le_mul_of_nonneg_right coeffFee (pow_nonneg x0 _)) cap (pow_nonneg (mass_nonneg ..) _) (by positivity)
    _=(x^i*x^(n-i+1))*((n:ℝ)+2)*M^(n+1)*|coeff i A|:=by ring
    _=_:=by rw [←pow_add,show i+(n-i+1)=n+1 by omega];rfl

theorem stable (n:ℕ)(A:Cost){x r s T:ℝ}(x0:0 ≤ x)(x1:x ≤ 1)(one:1 ≤ T)(paid:max |r| |s| ≤ T):
    |measured n A x r-measured n A x s|  ≤  |r-s| *((n:ℝ)+1)*T^n*mass n A:=by
  rw [placed,placed,←sum_sub_distrib];unfold mass;rw [mul_sum]
  apply (abs_sum_le_sum_abs ..).trans;apply sum_le_sum;intro i hi
  have hn:i ≤ n:=mem_range_succ_iff.mp hi
  have sep:=abs_pow_sub_pow_le r s (i+1)
  have fare:(max |r| |s|)^((i+1)-1) ≤ T^n:=by
    rw [Nat.add_sub_cancel];exact (pow_le_pow_left₀ ((abs_nonneg _).trans (le_max_left ..)) paid i).trans (pow_le_pow_right₀ one hn)
  have seat:((i+1:ℕ):ℝ) ≤ (n:ℝ)+1:=by exact_mod_cast Nat.succ_le_succ hn
  rw [←mul_sub,abs_mul,abs_mul,abs_of_nonneg (pow_nonneg x0 _)]
  calc
    _ ≤ |coeff i A| *(|r-s| *((n:ℝ)+1)*T^n):=by
      apply mul_le_mul (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ x0 x1)) _ (abs_nonneg _) (abs_nonneg _)
      exact sep.trans (mul_le_mul (mul_le_mul_of_nonneg_left seat (abs_nonneg _)) fare (by positivity) (by positivity))
    _=_:=mul_comm ..

end YM.Integration.WilsonSeparatedPrefixKineticChart
end
