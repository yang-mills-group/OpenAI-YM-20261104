import YM.RegulatorIR.Momentum.Movement

/-! Local/far quota payment by difference bounds on the joint grid. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent
open scoped Topology ENNReal NNReal BigOperators Classical
variable {J X:Type} {c b L:ℝ≥0∞} {W : X→ℝ≥0∞} [Fintype J] [DecidableEq J]
def extent (v:Moves J) :ℝ≥0∞:= (size v:ℝ≥0∞)
omit [DecidableEq J] in
@[simp] lemma extent_zero : extent (0:Moves J)=0:=by simp [extent,Laurent.size]
private lemma span_b {v:Moves J} (h:v≠0):∃ i:J,∃ u:Moves J,size v=size u+1 ∧ (v=u+hop i ∨ v=u-hop i):=by
 obtain ⟨i,ht⟩:∃ i:J,v i≠0:= Function.ne_iff.mp h
 rcases lt_or_gt_of_ne ht with H|H
 · refine ⟨i,v+hop i,?_,Or.inr (by simp)⟩
   simp only [size,Pi.add_apply,hops]; rw [← add_sum_erase _ _ (mem_univ i),← add_sum_erase _ (fun j=>(v j+if j=i then 1 else 0).natAbs) (mem_univ i)]
   rw [sum_congr rfl (show ∀ j∈Finset.univ.erase i,(v j+ if j=i then 1 else 0).natAbs=(v j).natAbs from fun j hj=>by rw [if_neg (mem_erase.mp hj).1,add_zero]),if_pos rfl];omega
 refine ⟨i,v-hop i,?_,Or.inl (by simp)⟩
 simp only [size,Pi.sub_apply,hops]; rw [← add_sum_erase _ _ (mem_univ i),← add_sum_erase _ (fun j=>(v j-if j=i then 1 else 0).natAbs) (mem_univ i)]
 rw [sum_congr rfl (show ∀ j∈Finset.univ.erase i,(v j- if j=i then 1 else 0).natAbs=(v j).natAbs from fun j hj=>by rw [if_neg (mem_erase.mp hj).1,sub_zero]),if_pos rfl];omega

private lemma foils (T:Moves J→X→ℝ)(p:ℕ) (hp:T 0=0)(h:∀ i v,extent v≤L → quota (spring T i v) W ≤ (extent v+1)^p*c) v (hv:extent v ≤ L) : quota (T v) W ≤ (extent v+1)^(p+1)*c:=by
 generalize he:size v=n
 -- use suffices
 suffices ∀ m:ℕ,∀ v: Moves J,size v=m → extent v≤L→ quota (T v) W≤(extent v+1)^(p+1)*c from this _ _ rfl hv
 intro m; induction m using Nat.strong_induction_on with
 | h m ih=>
    intro v hz hv; by_cases hf:v=0
    · rw [hf,hp,quota_zero]; exact bot_le
    obtain ⟨i,u,he,Hu⟩:=span_b hf; have hl: extent v=extent u+1:=by unfold extent;rw [he]; exact_mod_cast rfl
    have hh:extent u ≤ extent v:=hl ▸ le_self_add
    have hp:= (ih (size u) (hz ▸ (he ▸ Nat.lt_add_one _)) u rfl (hh.trans hv))
    have ht:quota (T v-T u) W≤(extent v+1)^p*c:=by
       rcases Hu with H|H
       · apply le_trans (b:=(extent u+1)^p*c) (H ▸ h i u (hh.trans hv)); gcongr
       rw [← quota_neg,neg_sub]; exact (show T u-T v=spring T i v from by rw [spring,H]; simp).symm ▸ h i v hv
    nth_rewrite 1 [show T v=T v-T u+T u from (sub_add_cancel ..).symm]
    apply (quota_add _ _ _).trans ((add_le_add ht hp).trans ?_); rw [← add_mul]; apply mul_le_mul_left _
    calc
       _ ≤ (extent v+1)^p + (extent v+1)^p*(extent u+1):=by gcongr;rw [pow_succ (extent u+1)];gcongr
       _ = _:= by rw [pow_succ,show extent u+1=extent v from hl.symm,mul_add,mul_one,add_comm]
lemma total_rest (T:Moves J→X→ℝ)(p:ℕ)(h:∀ t:List J,t.length=p→ ∀ v,extent v≤L → quota (journey T t v) W ≤c)(v:Moves J)(hv:extent v ≤ L): quota (rest T p v) W ≤ (extent v+1)^p*c:=by
 induction p generalizing T v with
 | zero=>simpa only [rest,deposit,range_zero,sum_empty,sub_zero,pow_zero,one_mul] using (show quota (T v) W≤c from h [] rfl v hv)
 | succ p ih=>
    apply foils _ _ (debt ..) _ v hv;intro j v hv;rw [move_due];exact ih (spring T j) (fun t ht=> h (j::t) (by simp [ht])) v hv

private lemma rise_size (i:J) (v:Moves J) : extent (v-hop i)≤extent v+1:=by
 unfold extent; norm_cast; rw [sub_eq_add_neg]; have hv : size (-hop i)=1:=by simp only [size,Pi.neg_apply,hops,Int.natAbs_neg];rw [Finset.sum_eq_single i (fun j _ hj=>by simp [hj]) (fun h=>False.elim (h (mem_univ _)))]; simp
 rw [← hv]; exact size_add ..
omit [DecidableEq J] in
private lemma reach_cast (i:J)(v:Moves J): ‖(v i:ℝ)‖ₑ ≤ extent v:=by
 unfold extent; rw [← ofReal_norm,Real.norm_eq_abs, ←Int.cast_abs]; exact_mod_cast (show |v i|≤ (size v:ℤ) from Int.natCast_natAbs (v i) ▸ (by exact_mod_cast single_le_sum (s:=Finset.univ) (f:=fun i=> (v i).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i) : (((v i).natAbs:ℤ) ≤ (size v:ℤ))))

def height (n:ℕ):ℝ≥0∞:= 2^(n*n)
lemma height_f (n:ℕ): height n ≠⊤:=by unfold height; finiteness
lemma particles_cost (n) (v:Moves J)(u:Sequence J n): ‖rateP n u v‖ₑ ≤ height n * (extent v+1)^n:=by
 induction n generalizing v with
 | zero=>simp [rateP,height]
 | succ n ih=>
    rw [rateP,enorm_mul]; apply mul_le_mul' (le_trans (reach_cast (u 0) v) (show extent v ≤ extent v+1 from le_self_add)) (ih _ _) |>.trans
    let p:=extent v
    calc
       _ ≤ (p+1)*(height n*(2*(p+1))^n):=by
         gcongr; have hx:= add_le_add_left (rise_size (u 0) v) 1
         exact hx.trans (by change p+1+1≤2*(p+1);rw [two_mul];gcongr; exact le_add_self)
       _ = (height n*2^n)*(p+1)^(n+1):=by rw [mul_pow,pow_succ];ring
       _ ≤ _:= mul_le_mul_left (by unfold height; rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by nlinarith)) _

def feeP (J:Type)[Fintype J] (n:ℕ):ℝ≥0∞:= (Fintype.card (Sequence J n):ℝ≥0∞) * height n
omit [DecidableEq J] in
lemma fee_f (n):feeP J n≠⊤:=by unfold feeP height;finiteness
lemma inverse_f (n:ℕ): ‖((Nat.factorial n:ℝ))⁻¹‖ₑ ≤ 1:=by
 rw [← ENNReal.ofReal_one, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
 refine ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ ?_); exact_mod_cast Nat.factorial_pos n
lemma portion_cost (U:Moves J→X→ℝ)(n:ℕ)(hv:∀ i: Sequence J n, quota (journey U (stamps n i) 0) W ≤ c) (v:Moves J) : quota (portion n U v) W ≤ feeP J n * ((extent v+1)^n*c) :=by
 rw [particles, show ∀ (p:X→ℝ)(r:ℝ), quota (r • p) W= ‖r‖ₑ * quota p W from fun p r=> quota_times p W r]; refine le_trans (mul_le_mul' (inverse_f n) (quota_sum ..)) ?_;rw [one_mul,feeP,mul_assoc, ← nsmul_eq_mul,← card_univ,← sum_const]; apply sum_le_sum; intro i _; exact (quota_times _ W _).trans_le ((mul_le_mul' (particles_cost n v i) (hv i)).trans_eq (mul_assoc ..))
end YM.RegulatorIR.Momentum
