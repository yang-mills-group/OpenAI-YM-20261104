import YM.Integration.WilsonPhysicalMarkedDefectRawCash

/-! The finite complex power-series estimate used by signed marked partitions.
The finite diagonal calculation follows the original Bakery.under_p; the
absolute polynomial product uses Bakery.Belt_product on the two true
coefficient majorants. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.RawProduct
open PowerSeries Finset MSbar MSbar.Bakery RawBank
open scoped BigOperators Classical

def value (p:ℕ) (z:ℂ) (T:PowerSeries ℂ):ℂ:=∑e∈Finset.range (p+1),z^e*coeff e T
def belt (p:ℕ) (T:PowerSeries ℂ):ℝ:=∑e∈Finset.range (p+1),‖coeff e T‖
private def weights (T:PowerSeries ℂ):PowerSeries ℝ:=PowerSeries.mk (fun e=>‖coeff e T‖)

theorem entries (n:ℕ) (A B:PowerSeries ℂ):belt n (A*B)≤belt n A*belt n B:=by
  have term (k:ℕ):‖coeff k (A*B)‖≤coeff k (weights A*weights B):=by
    rw [Cacao.elevator,Cacao.elevator]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>?_ )
    simp only [weights,coeff_mk,norm_mul]
    exact le_refl _
  calc
    _≤Belt n (weights A*weights B):=Finset.sum_le_sum (fun k _=>(term k).trans (le_abs_self _))
    _≤Belt n (weights A)*Belt n (weights B):=Belt_product .. 
    _=_:=by simp [Belt,belt,weights]

theorem bounded (p:ℕ) {g:ℝ} (gp:0≤g) (small:g≤1) (A:PowerSeries ℂ) :
    ‖cash p g A‖≤belt p A:=by
  unfold cash belt
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>?_ )
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg gp]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ gp small)

theorem under (n:ℕ) (v:ℂ) (A B:PowerSeries ℂ) : value n v (A*B)=
    ∑i∈range (n+1),∑j∈range (n+1),if i+j≤n then v^(i+j)*(coeff i A*coeff j B) else 0:=by
    let e i j:=v^(i+j:ℕ)*(coeff i A*coeff j B); let r:=range (n+1); let g i a j:= if i+j=a then e i j else 0
    have he(i j) : ∑ k∈r,g i k j=if i+j≤n then e i j else 0:=by unfold g r; simp only [Finset.sum_ite_eq, mem_range,Nat.lt_succ_iff]
    have hz(i a)(ha:a∈r): ∑ j∈r,g i a j= if i≤a then e i (a-i) else 0:=by
       have hh:=mem_range.mp ha; by_cases he:i ≤ a
       · rw [if_pos he,sum_eq_single_of_mem (a-i) (mem_range.mpr (by omega)),show g i _ _=_ from if_pos (by omega:i+(a-i)=a)]; exact fun j hj hx=> if_neg (by omega:i+j≠a)
       rw [if_neg he]; exact sum_eq_zero fun j hj=> if_neg (by omega : i+j≠ a)
    conv_rhs => arg 2; ext; arg 2; ext; rw [← he]
    unfold value; have hh(a)(ha:a∈r):v^a*coeff a (A*B)= ∑ i∈r, ∑ j∈r,g i a j:=by
        simp_rw [hz _ _ ha]; rw [Cacao.elevator, Finset.mul_sum, ← sum_subset (s₁:=range (a+1)) (s₂:=r) (range_mono (mem_range.mp ha))]
        · apply Finset.sum_congr rfl; intro i hi; have hi:i≤a:= Nat.lt_succ_iff.mp (mem_range.mp hi);rw [if_pos hi]; unfold e; rw [Nat.add_sub_of_le hi] -- i+a-i? lemma
        intro j hj ht; exact if_neg (by simpa [Nat.lt_succ_iff] using ht)
    calc
       _ = ∑ a∈r,∑ i∈r,∑ j∈r,g i a j:=sum_congr rfl hh
       _ = _ :=by rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [sum_comm]

theorem response (p:ℕ) {g:ℝ} (gp:0≤g) (small:g≤1) (A B:PowerSeries ℂ) :
    ‖cash p g (A*B)-cash p g A*cash p g B‖≤g^(p+1)*(belt p A*belt p B):=by
  change ‖value p (g:ℂ) (A*B)-value p (g:ℂ) A*value p (g:ℂ) B‖≤_
  rw [under]
  unfold value belt
  rw [sum_mul,sum_mul (f:=fun i=>‖coeff i A‖),mul_sum,←sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum (fun i _=>?_))
  rw [mul_sum,mul_sum,mul_sum,←sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _=>?_)
  split
  · rw [pow_add,show (g:ℂ)^i*(g:ℂ)^j*(coeff i A*coeff j B)-((g:ℂ)^i*coeff i A)*((g:ℂ)^j*coeff j B)=0 by ring,norm_zero]
    positivity
  · rw [zero_sub,norm_neg,show (g:ℂ)^i*coeff i A*((g:ℂ)^j*coeff j B)=(g:ℂ)^(i+j)*(coeff i A*coeff j B) by ring,norm_mul,norm_mul,
      norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg gp]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one gp small (by omega)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end YM.Integration.WilsonPhysicalMarkedDefect.RawProduct
