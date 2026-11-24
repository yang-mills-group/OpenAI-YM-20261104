import YM.Integration.WilsonPosteriorProjectionStencil

/-! On a complete translated grid the other fields are held fixed when the coordinate
occupied by a derivative of the unit moves. Only Taylor remainders on its own support enter. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSmoothUnitLatticeDifference
open Set Finset YM.LocalLTE.Weft YM.Integration.WilsonPosteriorProjectionStencil
open scoped BigOperators Classical

theorem counted {α:Type}[Fintype α](k:ℕ)(t:ℝ)(f:α → ℝ)(change:J k → α ≃ α)
    (a:α → J k → ℝ)(E:α → ℝ)
    (remainder:∀l z,|∑i:J k,a z i*(t*probe k l)^i.val - f (change l z)|  ≤  E z)
    (j:J k)(hj:j≠0):
    |(∑z,a z j)*t^j.val|  ≤  cost k j*(∑z,E z):=by
  let total(i:J k):ℝ:=(∑z,a z i)-(if i=0 then ∑z,f z else 0)
  have bound (l:J k):|∑i:J k,total i*(t*probe k l)^i.val|  ≤  ∑z,E z:=by
    let s:=t*probe k l
    have paid:|∑z,((∑i:J k,a z i*s^i.val)-f (change l z))| ≤ ∑z,E z:=
      (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun z _=>remainder l z)
    have turn:∑z,f (change l z)=∑z,f z:=(change l).sum_comp f
    have offset:∑i:J k,(if i=0 then ∑z,f z else 0)*s^i.val=∑z,f z:=by
      simp only [ite_mul,zero_mul]
      simp
    change |∑i:J k,((∑z,a z i)-(if i=0 then ∑z,f z else 0))*s^i.val| ≤ _
    simp_rw [sub_mul,sum_mul]
    rw [sum_sub_distrib,offset,sum_comm]
    rw [sum_sub_distrib,turn] at paid
    exact paid
  simpa only [total,if_neg hj,sub_zero] using price k total j t (∑z,E z) bound

def coef (f:ℝ → ℝ)(x:ℝ)(i:ℕ):ℝ:=((i.factorial:ℝ)⁻¹)*iteratedDeriv i f x

private theorem expansion (f:ℝ → ℝ)(m:ℕ)(a t s:ℝ)(ht:0<t)
    (smooth:ContDiff ℝ (↑(m+1):WithTop ℕ∞) f):
    (∑i:Fin (m+1),coef f a i.val*s^i.val)=taylorWithinEval f m (Icc a (a+t)) a (a+s):=by
  rw [taylor_within_apply,Fin.sum_univ_eq_sum_range (fun i:ℕ=>coef f a i*s^i)]
  apply sum_congr rfl
  intro i hi
  have degree:i ≤ m+1:=by have:=Finset.mem_range.mp hi;omega
  have sm:ContDiffAt ℝ i f a:=(smooth.of_le (by exact_mod_cast degree)).contDiffAt
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith: a<a+t)) sm
    (show a∈Icc a (a+t) from ⟨le_rfl,by linarith⟩)]
  simp only [coef,add_sub_cancel_left,smul_eq_mul]
  ring

theorem smooth {α:Type}[Fintype α](k:ℕ)(live:0<k)(t:ℝ)(ht:0<t)(x:α → ℝ)
    (f:ℝ → ℝ)(regular:ContDiff ℝ (↑(2*k+1):WithTop ℕ∞) f)(change:J k → α ≃ α)
    (values:∀z l,f (x z+t*probe k l)=f (x (change l z)))
    (mass:α → ℝ)(nonneg:∀z,0 ≤ mass z)
    (heads:∀z y,y∈Icc (x z) (x z+t) → |iteratedDeriv (2*k+1) f y| ≤ mass z):
    |∑z,deriv f (x z)|  ≤  cost k ⟨1,by omega⟩*(∑z,mass z)*t^(2*k):=by
  let j:J k:=⟨1,by omega⟩
  have data(l:J k)(z:α):|∑i:J k,coef f (x z) i.val*(t*probe k l)^i.val-f (x (change l z))|
       ≤  mass z*t^(2*k+1):=by
    let a:=x z
    let s:=t*probe k l
    have hs:0 ≤ s:=mul_nonneg ht.le (probes k l).1.le
    have st:s ≤ t:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left (probes k l).2 ht.le
    have inc:a+s∈Icc a (a+t):=by exact ⟨by linarith,by linarith⟩
    have wage(y:ℝ)(hy:y∈Icc a (a+t)):‖iteratedDerivWithin (2*k+1) f (Icc a (a+t)) y‖ ≤ mass z:=by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith:a<a+t)) regular.contDiffAt hy]
      exact heads z y hy
    have pay:=taylor_mean_remainder_bound (n:=2*k) (by linarith:a ≤ a+t)
      regular.contDiffOn inc wage
    rw [←values z l,expansion f (2*k) a t s ht regular,abs_sub_comm]
    have H:1 ≤ ((2*k).factorial:ℝ):=by exact_mod_cast Nat.factorial_pos (2*k)
    calc _  ≤  mass z*s^(2*k+1)/(2*k).factorial:=by simpa only [Real.norm_eq_abs,add_sub_cancel_left] using pay
         _  ≤  mass z*s^(2*k+1):=div_le_self (mul_nonneg (nonneg z) (pow_nonneg hs _)) H
         _  ≤  _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs st _) (nonneg z)
  have obs:=counted k t (fun z=>f (x z)) change (fun z i=>coef f (x z) i.val)
    (fun z=>mass z*t^(2*k+1)) data j (by intro h;have bad:=congrArg Fin.val h;norm_num [j] at bad)
  rw [←sum_mul] at obs
  have c1(z:α):coef f (x z) j.val=deriv f (x z):=by simp [coef,j]
  have once:t^j.val=t:=by change t^1=t;exact pow_one _
  simp_rw [c1] at obs
  rw [once,abs_mul,abs_of_pos ht,pow_succ t (2*k)] at obs
  apply (le_of_mul_le_mul_right _ ht)
  simpa only [mul_assoc] using obs

end YM.Integration.WilsonSmoothUnitLatticeDifference
