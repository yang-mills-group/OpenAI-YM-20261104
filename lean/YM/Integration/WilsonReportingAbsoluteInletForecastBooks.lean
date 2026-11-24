import YM.FormalBulk08.Wine.Ink
import Mathlib.RingTheory.PowerSeries.Basic

/-! Numerical truncation on the two original independent Wilson books.
Their product is the genuine formal unit. The off-diagonal finite terms
first occur at the next unpurchased power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastBooks
open Finset PowerSeries FormalBulk08.Wine
open scoped Classical BigOperators

def value (n:ℕ) (f:PowerSeries ℝ) (g:ℝ):ℝ:=∑i∈range (n+1),g^i*coeff i f
def mass (n:ℕ) (f:PowerSeries ℝ):ℝ:=∑i∈range (n+1),|coeff i f|

theorem exact (D:PowerSeries ℝ):coeff 0 (bookU D)=1 ∧ coeff 0 (bookH D)=1 ∧ bookH D*bookU D=1:=
  ⟨book_guard D,book_fresh D,book_equal D⟩

private theorem head (n:ℕ)(g:ℝ):value n 1 g=1:=by
  classical
  simp [value,PowerSeries.coeff_one]

private theorem convolution (n:ℕ)(v:ℝ) (A B : PowerSeries ℝ) : value n (A*B) v = ∑ i∈ range (n+1),∑ j∈range (n+1), if i+j ≤ n then v^(i+j)*(coeff i A*coeff j B) else 0 :=by
    let e i j:=v^(i+j:ℕ)*(coeff i A*coeff j B); let r:=range (n+1); let g i a j:= if i+j=a then e i j else 0
    have he(i j) : ∑ k∈r,g i k j=if i+j≤n then e i j else 0:=by unfold g r; simp only [Finset.sum_ite_eq, mem_range,Nat.lt_succ_iff]
    have hz(i a)(ha:a∈r): ∑ j∈r,g i a j= if i≤a then e i (a-i) else 0:=by
       have hh:=mem_range.mp ha; by_cases he:i ≤ a
       · rw [if_pos he,sum_eq_single_of_mem (a-i) (mem_range.mpr (by omega)),show g i _ _=_ from if_pos (by omega:i+(a-i)=a)]; exact fun j hj hx=> if_neg (by omega:i+j≠a)
       rw [if_neg he]; exact sum_eq_zero fun j hj=> if_neg (by omega : i+j≠ a)
    conv_rhs => arg 2; ext; arg 2; ext; rw [← he]
    unfold value; have hh(a)(ha:a∈r):v^a*coeff a (A*B)= ∑ i∈r, ∑ j∈r,g i a j:=by
        simp_rw [hz _ _ ha]; rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum, ← sum_subset (s₁:=range (a+1)) (s₂:=r) (range_mono (mem_range.mp ha))]
        · apply Finset.sum_congr rfl; intro i hi; have hi:i≤a:= Nat.lt_succ_iff.mp (mem_range.mp hi);rw [if_pos hi]; unfold e; rw [Nat.add_sub_of_le hi] -- i+a-i? lemma
        intro j hj ht; exact if_neg (by simpa [Nat.lt_succ_iff] using ht)
    calc
       _ = ∑ a∈r,∑ i∈r,∑ j∈r,g i a j:=sum_congr rfl hh
       _ = _ :=by rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [sum_comm]
private theorem multiply (n:ℕ) (v:ℝ) (hV:0 ≤ v)(hv:v≤1) (A B:PowerSeries ℝ) : |value n (A*B) v-value n A v*value n B v|≤ v^(n+1)*(mass n A*mass n B):=by
   rw [convolution]; unfold value mass; rw [sum_mul,sum_mul (f:=fun i=> |coeff i A|),mul_sum,← sum_sub_distrib]
   refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun i _=>?_)); rw [mul_sum,mul_sum,mul_sum,← sum_sub_distrib]; apply (abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun j _=>?_); split; next he=> rw [pow_add,show v^i*v^j*(coeff i A*coeff j B) - (v^i*coeff i A)*(v^j*coeff j B)=0 from (by ring),abs_zero]; positivity
   next hh=>
     rw [zero_sub,abs_neg,show v^i*coeff i A*(v^j*coeff j B)=v^(i+j)*(coeff i A*coeff j B) by ring,abs_mul,abs_mul, abs_of_nonneg (pow_nonneg hV _)]
     exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hV hv (by omega)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
theorem truncation (n:ℕ)(D:PowerSeries ℝ){g:ℝ}(g0:0≤g)(g1:g≤1):
    |1-value n (bookH D) g*value n (bookU D) g|≤g^(n+1)*(mass n (bookH D)*mass n (bookU D)):=by
  have h:=multiply n g g0 g1 (bookH D) (bookU D)
  rw [book_equal,head] at h
  exact h

theorem reciprocal (n:ℕ)(D:PowerSeries ℝ){g:ℝ}(g0:0≤g)(g1:g≤1)
    (paid:1/4≤value n (bookU D) g):
    |(value n (bookU D) g)⁻¹-value n (bookH D) g|≤4*g^(n+1)*(mass n (bookH D)*mass n (bookU D)):=by
  let t:=value n (bookU D) g
  let h:=value n (bookH D) g
  have t0:0<t:=lt_of_lt_of_le (by norm_num:0<(1:ℝ)/4) paid
  let b:=g^(n+1)*(mass n (bookH D)*mass n (bookU D))
  have raw:|1-h*t|≤b:=truncation n D g0 g1
  have diff:|(t⁻¹-h)*t|≤b:=by rwa [sub_mul,inv_mul_cancel₀ t0.ne'] 
  rw [abs_mul,abs_of_pos t0] at diff
  have low:=mul_le_mul_of_nonneg_left paid (abs_nonneg (t⁻¹-h))
  change |t⁻¹-h|≤4*g^(n+1)*(mass n (bookH D)*mass n (bookU D))
  change |t⁻¹-h| *t≤g^(n+1)*(mass n (bookH D)*mass n (bookU D)) at diff
  linarith only [low,diff]

end YM.Integration.WilsonReportingAbsoluteInletForecastBooks
