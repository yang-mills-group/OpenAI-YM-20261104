import YM.Integration.WilsonPositionScaleLawGuardPoly

/-! Uniform finite-degree and numerical coefficient bounds for the actual
noncommuting substitution invoice over a whole set of scale ratios. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardStock
open Finset PowerSeries
open WilsonPositionScaleLawGuardPoly (mass)
open scoped Classical Polynomial BigOperators
variable {I R:Type*}[NormedRing R]
def Stock(p:I→R[X]):Prop:=∃N:ℕ,∃C:ℝ,0≤C ∧ ∀x,(p x).natDegree≤N ∧ ∀k,‖(p x).coeff k‖≤C

theorem plus {p z:I→R[X]}(a:Stock p)(b:Stock z):Stock (fun x=>p x+z x):=by
  obtain ⟨N,A,hA,ha⟩:=a;obtain ⟨M,B,hB,hb⟩:=b
  refine ⟨max N M,A+B,add_nonneg hA hB,fun x=>⟨(Polynomial.natDegree_add_le ..).trans (max_le_max (ha x).1 (hb x).1),?_⟩⟩
  intro k;rw [Polynomial.coeff_add];exact (norm_add_le ..).trans (add_le_add ((ha x).2 k) ((hb x).2 k))

theorem minus {p z:I→R[X]}(a:Stock p)(b:Stock z):Stock (fun x=>p x-z x):=by
  obtain ⟨N,A,hA,ha⟩:=a;obtain ⟨M,B,hB,hb⟩:=b
  refine ⟨max N M,A+B,add_nonneg hA hB,fun x=>⟨(Polynomial.natDegree_sub_le ..).trans (max_le_max (ha x).1 (hb x).1),?_⟩⟩
  intro k;rw [Polynomial.coeff_sub];exact (norm_sub_le ..).trans (add_le_add ((ha x).2 k) ((hb x).2 k))

theorem times {p z:I→R[X]}(a:Stock p)(b:Stock z):Stock (fun x=>p x*z x):=by
  obtain ⟨N,A,hA,ha⟩:=a;obtain ⟨M,B,hB,hb⟩:=b
  refine ⟨N+M,((N+M+1:ℕ):ℝ)*(A*B),by positivity,fun x=>?_⟩
  have d:((p x)*(z x)).natDegree≤N+M:=(Polynomial.natDegree_mul_le ..).trans (Nat.add_le_add (ha x).1 (hb x).1)
  refine ⟨d,fun k=>?_⟩
  by_cases hk:k≤N+M
  · rw [Polynomial.coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    calc _≤∑i∈range (k+1),‖(p x).coeff i*(z x).coeff (k-i)‖:=norm_sum_le _ _
         _≤∑_∈range (k+1),A*B:=by
           apply Finset.sum_le_sum;intro i _;exact (norm_mul_le _ _).trans (mul_le_mul ((ha x).2 _) ((hb x).2 _) (norm_nonneg _) hA)
         _=((k+1:ℕ):ℝ)*(A*B):=by simp [nsmul_eq_mul]
         _≤_:=mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hk 1) (mul_nonneg hA hB)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (d.trans_lt (lt_of_not_ge hk)),norm_zero];positivity


theorem printed (q:ℕ)(a:I→PowerSeries R){C:ℝ}(hC:0≤C)(h:∀x k,k≤q→‖coeff k (a x)‖≤C):
    Stock (fun x=>trunc (q+1) (a x)):=by
  refine ⟨q,C,hC,fun x=>⟨Nat.le_of_lt_succ (natDegree_trunc_lt _ _),fun k=>?_⟩⟩
  rw [coeff_trunc];split_ifs with hk
  · exact h _ _ (by omega)
  · simpa only [norm_zero] using hC

theorem cost {p:I→R[X]}(s:Stock p):∃T:ℝ,0≤T ∧ ∀x,mass (p x)≤T:=by
  obtain ⟨N,C,hC,paid⟩:=s
  refine ⟨((N+1:ℕ):ℝ)*C,by positivity,fun x=>?_⟩
  have sub:(p x).support⊆range (N+1):=fun j hj=>Finset.mem_range.mpr
    (Nat.lt_succ_of_le ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans (paid x).1))
  calc
    _≤∑_∈(p x).support,C:=Finset.sum_le_sum fun k _=>(paid x).2 k
    _≤∑_∈range (N+1),C:=Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _=>hC)
    _=_:=by simp [nsmul_eq_mul]

theorem fixed (p:R[X]):Stock (fun _:I=>p):=by
  have pos:0≤ mass p:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨p.natDegree,mass p,pos,fun _=>⟨le_rfl,fun k=>?_⟩⟩
  by_cases h:k∈p.support
  · exact Finset.single_le_sum (fun j _=>norm_nonneg (p.coeff j)) h
  · rw [Polynomial.notMem_support_iff.mp h,norm_zero];exact pos

theorem powers {p:I→R[X]}(s:Stock p)(j:ℕ):Stock (fun x=>p x^j):=by
  induction j with
  | zero=>simpa only [pow_zero] using fixed (I:=I) (1:R[X])
  | succ j ih=>simpa only [pow_succ] using times ih s

theorem many {ι:Type*}(v:Finset ι)(p:ι→I→R[X])(s:∀i∈v,Stock (p i)):
    Stock (fun x=>∑i∈v,p i x):=by
  classical
  induction v using Finset.induction_on with
  | empty=>simpa only [Finset.sum_empty] using fixed (I:=I) (0:R[X])
  | insert i v hi ih=>
    simp only [Finset.sum_insert hi]
    exact plus (s i (Finset.mem_insert_self _ _)) (ih (fun j hj=>s j (Finset.mem_insert_of_mem hj)))

end YM.Integration.WilsonPositionScaleLawGuardStock
