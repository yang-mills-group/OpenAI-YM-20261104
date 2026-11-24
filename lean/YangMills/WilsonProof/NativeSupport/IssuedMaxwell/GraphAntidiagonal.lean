import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ExteriorReceipt
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphAntidiagonal
open YM YM.FVA2 YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Enh
open PowerSeries
open scoped BigOperators Classical
variable {G:Gauge}{n m:ℕ}

theorem salary (a b:PowerSeries ℂ)(c:ℂ)(k:ℕ):
    coeff k ((C c*a)*b)=c*∑j:Fin (k+1),coeff j.val a*coeff (k-j.val) b:=by
  rw [mul_assoc,coeff_C_mul,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j=>coeff i a*coeff j b),Fin.sum_univ_eq_sum_range (fun i=>coeff i a*coeff (k-i) b) (k+1)]

theorem original (A:Album G)(u:Scan G n)(v:Scan G m)(p:FLog G n)(h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    coeff k (Lamp A h y v (pack u t (p t x)))=
    ∑w:Fin (h+1),∑j:Fin (k+1),
      (Real.exp (((totalG u:ℝ)-(w.val:ℝ))*t):ℂ)*
        ∑i:Grade G w.val,coeff j.val (p t x (own i))*coeff (k-j.val) (lonelyG A y (own i) v):=by
  rw [Lamp,map_sum,←Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun w _=>?_
  rw [Settle,map_sum]
  have scale (i:Grade G w.val):fee t ((heft (own i):ℝ)-(totalG u:ℝ))=
      (Real.exp (((totalG u:ℝ)-(w.val:ℝ))*t):ℂ):=by
    unfold fee
    congr 2
    change -t*((w.val:ℝ)-(totalG u:ℝ)) = _
    ring
  unfold pack
  simp_rw [salary,scale,Finset.mul_sum]
  rw [Finset.sum_comm]
end IssuedMaxwell.GraphAntidiagonal
end
