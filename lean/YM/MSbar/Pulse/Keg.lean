import YM.MSbar.Bakery.Plate
import Mathlib.Analysis.SpecialFunctions.Exp
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery
open Function Filter MeasureTheory Cacao PowerSeries Finset
open scoped Topology Classical BigOperators
local notation "G"=> PowerSeries ℝ
local notation "µ"=>PowerSeries.coeff
variable {g h: PowerSeries ℝ}{κ ι :Type*}{α ε p K :ℝ}{n m : ℕ}
-- unweighted belt for rational products

def taste (p :ℕ)(g: PowerSeries ℝ)(x:ℝ) := ∑ i∈range (p+1),x^i*µ i g
def Belt (n:ℕ)(f:PowerSeries ℝ) :=∑ i∈range (n+1),|µ i f|
local notation "S"=> taste n
lemma Belt_pos (n:ℕ)(f:G):0 ≤ Belt n f:=sum_nonneg fun _ _=>abs_nonneg _
lemma Belt_entry (f:G)(n:ℕ)(i:ℕ)(h:i≤ n) : |µ i f| ≤ Belt n f:= single_le_sum (f:=fun i=>|µ i f|) (fun i _=> abs_nonneg _) (mem_range.mpr (by omega))
lemma taste_add (g h:G)(x:ℝ):taste n (g+h) x=taste n g x+taste n h x :=by unfold taste; simp only [_root_.map_add,mul_add,sum_add_distrib]
lemma taste_pays (hx:0≤α)(hv:α≤1)(f:G): |taste n f α| ≤ Belt n f := by
    unfold taste; refine (Finset.abs_sum_le_sum_abs ..).trans ?_; exact sum_le_sum fun i hi=> (abs_mul ..).trans_le (mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_of_nonneg (pow_nonneg hx _ )]; exact pow_le_one₀ hx hv))
lemma under_p (n:ℕ)(v:ℝ) (A B : G) : taste n (A*B) v = ∑ i∈ range (n+1),∑ j∈range (n+1), if i+j ≤ n then v^(i+j)*(µ i A*µ j B) else 0 :=by
    let e i j:=v^(i+j:ℕ)*(µ i A*µ j B); let r:=range (n+1); let g i a j:= if i+j=a then e i j else 0
    have he(i j) : ∑ k∈r,g i k j=if i+j≤n then e i j else 0:=by unfold g r; simp only [Finset.sum_ite_eq, mem_range,Nat.lt_succ_iff]
    have hz(i a)(ha:a∈r): ∑ j∈r,g i a j= if i≤a then e i (a-i) else 0:=by
       have hh:=mem_range.mp ha; by_cases he:i ≤ a
       · rw [if_pos he,sum_eq_single_of_mem (a-i) (mem_range.mpr (by omega)),show g i _ _=_ from if_pos (by omega:i+(a-i)=a)]; exact fun j hj hx=> if_neg (by omega:i+j≠a)
       rw [if_neg he]; exact sum_eq_zero fun j hj=> if_neg (by omega : i+j≠ a)
    conv_rhs => arg 2; ext; arg 2; ext; rw [← he]
    unfold taste; have hh(a)(ha:a∈r):v^a*µ a (A*B)= ∑ i∈r, ∑ j∈r,g i a j:=by
        simp_rw [hz _ _ ha]; rw [Cacao.elevator, Finset.mul_sum, ← sum_subset (s₁:=range (a+1)) (s₂:=r) (range_mono (mem_range.mp ha))]
        · apply Finset.sum_congr rfl; intro i hi; have hi:i≤a:= Nat.lt_succ_iff.mp (mem_range.mp hi);rw [if_pos hi]; unfold e; rw [Nat.add_sub_of_le hi] -- i+a-i? lemma
        intro j hj ht; exact if_neg (by simpa [Nat.lt_succ_iff] using ht)
    calc
       _ = ∑ a∈r,∑ i∈r,∑ j∈r,g i a j:=sum_congr rfl hh
       _ = _ :=by rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [sum_comm]
lemma Belt_product (f g:G)(n:ℕ): Belt n (f*g) ≤ Belt n f*Belt n g:=by
    let p(A:G):G:= PowerSeries.mk fun i=> |µ i A|; have he (A:G): Belt n A=taste n (p A) 1:=by unfold p taste Belt;simp
    have hp : Belt n (f*g) ≤ taste n (p f*p g) 1:=by
       unfold Belt taste; refine sum_le_sum fun i _=> ?_; rw [Cacao.elevator,Cacao.elevator]; simp only [one_pow,one_mul]; apply (abs_sum_le_sum_abs ..).trans; exact (sum_congr rfl fun i _=> by unfold p; rw [abs_mul,PowerSeries.coeff_mk,PowerSeries.coeff_mk]).le
    refine hp.trans ?_; rw [under_p]; unfold p Belt; simp_rw [coeff_mk,one_pow,one_mul]; rw [sum_mul]; refine sum_le_sum fun i _=> ?_; rw [mul_sum]; apply sum_le_sum; intro j _; split;exact le_rfl; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
lemma taste_mul (n:ℕ) (v:ℝ) (hV:0 ≤ v)(hv:v≤1) (A B:G) : |taste n (A*B) v-taste n A v*taste n B v|≤ v^(n+1)*(Belt n A*Belt n B):=by
   rw [under_p]; unfold taste Belt; rw [sum_mul,sum_mul (f:=fun i=> |µ i A|),mul_sum,← sum_sub_distrib]
   refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun i _=>?_)); rw [mul_sum,mul_sum,mul_sum,← sum_sub_distrib]; apply (abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun j _=>?_); split; next he=> rw [pow_add,show v^i*v^j*(µ i A*µ j B) - (v^i*µ i A)*(v^j*µ j B)=0 from (by ring),abs_zero]; positivity
   next hh=>
     rw [zero_sub,abs_neg,show v^i*µ i A*(v^j*µ j B)=v^(i+j)*(µ i A*µ j B) by ring,abs_mul,abs_mul, abs_of_nonneg (pow_nonneg hV _)]
     exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hV hv (by omega)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
lemma sauce (f:G)(n:ℕ)(h0 :0≤ α)(ht:α ≤1):|taste n f α-µ 0 f|≤ α *Belt n f :=by
   cases n with
   | zero=> simp [taste]; exact mul_nonneg h0 (Belt_pos ..)
   | succ n =>
       let g:=range (n+1); unfold taste Belt; rw [sum_range_succ',sum_range_succ' (f:= fun i=>|µ i f|),pow_zero,one_mul, add_sub_cancel_right,mul_add,mul_sum]; apply le_trans (abs_sum_le_sum_abs ..) (le_add_of_le_of_nonneg _ (mul_nonneg h0 (abs_nonneg _))); refine sum_le_sum fun i _=>?_ ; rw [abs_mul,abs_of_nonneg (pow_nonneg h0 _)]; exact mul_le_mul_of_nonneg_right (by simpa using (pow_le_pow_of_le_one h0 ht (by omega : 1 ≤ i+1))) (abs_nonneg _)
end YM.MSbar.Bakery
