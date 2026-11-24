import YM.RG11Proof.Travel.Driver

/-! # Thermometer derivative tests on FPS substitutions

Derivative **in s** of finite coefficient jets. Control finite truncation
INPUTS not global derivative rows. For `subst g(s) f` with f fixed need
Anchored g(s) for s in a neighborhood and thus g'0=0 (avoid order N+1 from
f in output equality with only N powers f). Here all s anchored in intended
flow use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Travel
open YM.RG11.Jets YM.RG11.Scale PowerSeries
open scoped BigOperators Classical Topology
local notation "ps"=>PowerSeries ℝ
variable {p q:ℝ → ps}{p' q':ps}{s:ℝ}{N:ℕ}

def Speed (p:ℝ→ps)(s:ℝ)(u:ps)(N:ℕ):Prop:=
    ∀ i≤N,HasDerivAt (fun t=>coeff i (p t)) (coeff i u) s
namespace Speed
 theorem rest (u:ps): Speed (fun _=>u) s 0 N:= fun i _=>by rw [map_zero]; exact hasDerivAt_const ..
protected theorem add (h:Speed p s p' N)(he:Speed q s q' N): Speed (fun u=>p u+q u) s (p'+q') N:= fun i hi=> by simp_rw [map_add]; exact (h _ hi).add (he _ hi)
protected theorem sum {I:Type*}{u: Finset I}{f:I→ ℝ→ps}{v:I→ps}(h:∀ i∈u,Speed (f i) s (v i) N):
     Speed (fun b=>∑i∈u,f i b) s (∑ i∈u,v i) N:= fun i hi=>by simp_rw [map_sum]; exact HasDerivAt.fun_sum (fun j hj=>h j hj i hi)
protected theorem mul (h:Speed p s p' N)(he:Speed q s q' N):
    Speed (fun u=>p u*q u) s (p'*q s+p s*q') N:=by
   intro i hi
   simp_rw [map_add,coeff_mul,← Finset.sum_add_distrib]; refine HasDerivAt.fun_sum (fun z hz=>?_)
   have ht:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz
   exact (h _ (by omega)).mul (he _ (by omega))
protected theorem pow (h:Speed p s p' N)(m:ℕ): Speed (fun u=>(p u)^m) s (((m:ℕ):ps)*(p s)^(m-1)*p') N:=by
   induction m with
   |zero=>simpa using Speed.rest (N:=N) (s:=s) 1
   |succ i ih=>
      have he:=ih.mul h
      cases i with
      |zero=>simpa using he
      |succ i=>
         convert! he using 1
         
         push_cast; simp only [pow_succ]; ring

protected theorem subst (h:Speed p s p' N)(ha:∀ u,Anchored (p u))(hp:Anchored p')(f:ps):
   Speed (fun u=> PowerSeries.subst (p u) f) s (PowerSeries.subst (p s) (derivative ℝ f) * p') N:=by
   intro i hi
   have hm(k:ℕ) := (h.pow k i hi |>.const_mul (coeff k f))
   have he:= HasDerivAt.fun_sum (u:=Finset.range (i+1)) (fun k _=>hm k)
   simp_rw [coeff_compose i f _ (ha _)]
   convert! he using 1
   rw [Finset.sum_range_succ']
   conv_rhs => rhs; simp
   rw [add_zero]
   push_cast
   let b (k:ℕ):ℝ:=coeff (k+1) f * (k+1)
   have title (k:ℕ): coeff (k+1) f * coeff i ((((k:ps)+1)*(p s)^k)*p')=b k*(coeff i ((p s)^k*p')):=by
     unfold b
     have H : (k:ps)+1=C ((k:ℝ)+1):=by rw [map_add,map_natCast,map_one]
     rw [H,mul_assoc,coeff_C_mul]; ring
   simp_rw [title]
   simp_rw [coeff_mul, coeff_compose _ _ _ (ha s), coeff_derivative,Finset.mul_sum,Finset.sum_mul,Finset.sum_comm (f:=fun (k:ℕ) (z:ℕ×ℕ)=> b k*(coeff z.1 ((p s)^k)*coeff z.2 p'))]
   apply Finset.sum_congr rfl; intro z hz
   have hz:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz
   by_cases ho:z.2=0
   · simp only [ho,coeff_zero_eq_constantCoeff_apply,show constantCoeff p'=0 from hp,mul_zero,Finset.sum_const_zero]
   -- summand with z.1 < k also vanishes by order
   apply Eq.trans _ (Finset.sum_subset (Finset.range_mono (show z.1+1 ≤ i from by omega)) (fun k _ hk=> ?_))
   · apply Finset.sum_congr rfl; intro j _; unfold b; ring
   simp only [Finset.mem_range] at hk
   have hu: coeff z.1 (p s^k)=0:=coeff_of_lt_order _ (lt_of_lt_of_le (b:=(k:ℕ∞)) (by exact_mod_cast (by omega:z.1 < k)) (le_order_pow_of_constantCoeff_eq_zero k (ha s)))
   rw [hu]; simp

 theorem gate {I:Type*}{f:I→ℝ→ps}{v:I→ps}(x: Finset I) (h:∀ i∈x,Speed (f i) s (v i) N):
    Speed (fun b:ℝ=> ∏ i∈x, f i b) s (∑ i∈x,v i*∏ j∈x.erase i,f j s) N:=by
    classical
    induction x using Finset.induction_on with
    | empty=>simpa using Speed.rest (s:=s) (N:=N) 1
    | insert i x hi ih=>
       have he:= (h i (by simp)).mul (ih (fun j hj=>h j (by simp [hj])))
       convert! he using 1
       · simp [hi]
       rw [Finset.sum_insert hi, Finset.erase_insert hi,Finset.mul_sum]; congr 1
       apply Finset.sum_congr rfl; intro j hj
       rw [Finset.erase_insert_of_ne (show i≠j from fun h=>hi (h ▸hj)),Finset.prod_insert (by simp [hi])]; ring
end Speed
end YM.RG11.Travel
