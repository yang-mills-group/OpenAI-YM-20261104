import YM.Integration.WilsonPositionScaleLawThermometerPrint

/-! A uniform price for the printed cubic over any jointly bounded family of
ordinary coefficients. All constants precede the coupling evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerStock
open Finset PowerSeries XSpace XSpace.Rose WilsonPositionScaleLawThermometerPrint
open scoped BigOperators Classical Polynomial
variable {I:Type*}
private def Stock(p:I→ℂ[X]):Prop:=∃N:ℕ,∃C:ℝ,0≤C ∧ ∀x,(p x).natDegree≤N ∧ ∀k,‖(p x).coeff k‖≤C

private theorem plus {p z:I→ℂ[X]}(a:Stock p)(b:Stock z):Stock (fun x=>p x+z x):=by
  obtain ⟨N,A,hA,ha⟩:=a;obtain ⟨M,B,hB,hb⟩:=b
  refine ⟨max N M,A+B,add_nonneg hA hB,fun x=>⟨(Polynomial.natDegree_add_le ..).trans (max_le_max (ha x).1 (hb x).1),?_⟩⟩
  intro k;rw [Polynomial.coeff_add];exact (norm_add_le ..).trans (add_le_add ((ha x).2 k) ((hb x).2 k))

private theorem minus {p z:I→ℂ[X]}(a:Stock p)(b:Stock z):Stock (fun x=>p x-z x):=by
  obtain ⟨N,A,hA,ha⟩:=a;obtain ⟨M,B,hB,hb⟩:=b
  refine ⟨max N M,A+B,add_nonneg hA hB,fun x=>⟨(Polynomial.natDegree_sub_le ..).trans (max_le_max (ha x).1 (hb x).1),?_⟩⟩
  intro k;rw [Polynomial.coeff_sub];exact (norm_sub_le ..).trans (add_le_add ((ha x).2 k) ((hb x).2 k))

private theorem times {p z:I→ℂ[X]}(a:Stock p)(b:Stock z):Stock (fun x=>p x*z x):=by
  obtain ⟨N,A,hA,ha⟩:=a;obtain ⟨M,B,hB,hb⟩:=b
  refine ⟨N+M,((N+M+1:ℕ):ℝ)*(A*B),by positivity,fun x=>?_⟩
  have d:((p x)*(z x)).natDegree≤N+M:=(Polynomial.natDegree_mul_le ..).trans (Nat.add_le_add (ha x).1 (hb x).1)
  refine ⟨d,fun k=>?_⟩
  by_cases hk:k≤N+M
  · rw [Polynomial.coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    calc _≤∑i∈range (k+1),‖(p x).coeff i*(z x).coeff (k-i)‖:=norm_sum_le _ _
         _≤∑_∈range (k+1),A*B:=by
           apply Finset.sum_le_sum;intro i _;rw [norm_mul];exact mul_le_mul ((ha x).2 _) ((hb x).2 _) (norm_nonneg _) hA
         _=((k+1:ℕ):ℝ)*(A*B):=by simp [nsmul_eq_mul]
         _≤_:=mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hk 1) (mul_nonneg hA hB)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (d.trans_lt (lt_of_not_ge hk)),norm_zero];positivity

variable (q:ℕ)(a:I→Badge→PowerSeries ℂ){C:ℝ}(hC:0≤C)(h:∀x s k,k≤q→‖coeff k (a x s)‖≤C)
include hC h in
private theorem raw (s:Badge):Stock (fun x=>trunc (q+1) (a x s)):=by
  refine ⟨q,C,hC,fun x=>⟨Nat.le_of_lt_succ (natDegree_trunc_lt _ _),fun k=>?_⟩⟩
  rw [coeff_trunc];split_ifs with hk
  · exact h _ _ _ (by omega)
  · simpa only [norm_zero] using hC

include hC h in
theorem original:∃T:ℝ,0≤T ∧ ∀x,mass q (a x)≤T:=by
  have slot:=raw q a hC h
  have face:=plus (plus (times (slot {0,1}) (slot {2})) (times (slot {0,2}) (slot {1}))) (times (slot {1,2}) (slot {0}))
  have three:=times (times (slot {0}) (slot {1})) (slot {2})
  have stock:Stock (fun x=>printed q (a x)):=by
    unfold printed cubic;simp only [two_mul];exact plus (minus (slot univ) face) (plus three three)
  obtain ⟨N,R,hR,hr⟩:=stock
  refine ⟨((N+1:ℕ):ℝ)*R,by positivity,fun x=>?_⟩
  have coeffSame {k:ℕ}(hk:k∈(fringe q (a x)).support):(fringe q (a x)).coeff k=(printed q (a x)).coeff k:=by
    have high:¬k≤q:=fun e=>(Polynomial.mem_support_iff.mp hk) (low q (a x) e)
    rw [fringe,Polynomial.coeff_sub,coeff_trunc,if_neg (by omega),sub_zero]
  have contain:(fringe q (a x)).support⊆range (N+1):=by
    intro k hk;apply mem_range.mpr
    have nn:(printed q (a x)).coeff k≠0:=by rw [←coeffSame hk];exact Polynomial.mem_support_iff.mp hk
    have d:=Polynomial.le_natDegree_of_ne_zero nn
    exact Nat.lt_succ_of_le (d.trans (hr x).1)
  calc mass q (a x)≤∑_∈(fringe q (a x)).support,R:=by
           apply Finset.sum_le_sum;intro k hk;rw [coeffSame hk];exact (hr x).2 _
       _≤∑_∈range (N+1),R:=Finset.sum_le_sum_of_subset_of_nonneg contain (fun _ _ _=>hR)
       _=((N+1:ℕ):ℝ)*R:=by simp [nsmul_eq_mul]

end YM.Integration.WilsonPositionScaleLawThermometerStock
end
