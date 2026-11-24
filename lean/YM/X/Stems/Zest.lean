import YM.X.Stems.Iota
/-!
Jet combinatorial: truncated first two live orders per vertex.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Jet
open Function Filter Gauss Finset
open scoped ContDiff BigOperators Classical
variable {I : Type*} {n m:ℕ} {f g:ℝ→ℝ}
variable {a b c d:ℝ}
structure Glow (n:ℕ)(f:ℝ→ℝ) (a b:ℝ) : Prop where
   nice : ContDiffAt ℝ ω f 0
   first : ∀ i<n,someJ f i=0
   live : someJ f n=a
   then1 : someJ f (n+1)=b
variable (hf:Glow n f a b)(hg:Glow m g c d)
namespace Glow
private lemma skip (i k:ℕ)(he:¬(i=n∧ k-i=m+1 ∨ i=n+1∧ k-i=m))(G: k=n+m+1)(hi:i≤k): i<n ∨ k-i<m:= by omega
lemma times (hf:Glow n f a b)(hg:Glow m g c d) : Glow (n+m) (f*g) (a*c) (a*d+b*c):= by
   refine ⟨hf.nice.mul hg.nice,fun i hi=> ?_,?_,?_⟩
   · rw [jo_mul hf.nice hg.nice]; apply Finset.sum_eq_zero; intro j hj; have hl:=Finset.mem_range.mp hj; rcases show j<n ∨ i-j<m from (by omega) with h|h <;> first| rw [hf.first _ h,zero_mul]|rw [hg.first _ h, mul_zero]
   · rw [jo_mul hf.nice hg.nice, Finset.sum_eq_single_of_mem n (by simp [Nat.lt_succ_iff]) (fun j hj hn=>?_), hf.live,Nat.add_sub_cancel_left,hg.live]; have he:=Finset.mem_range.mp hj; rcases show j<n∧n≤n ∨ n+m-j<m from (by omega) with h|h
     · rw [hf.first _ h.1,zero_mul]
     rw [hg.first _ h,mul_zero]
   rw [jo_mul hf.nice hg.nice]; let F (z:ℕ) := someJ f z * someJ g (n+m+1-z); let p:=Finset.range (n+m+1+1); have hn : n∈p:= by simp [p]; omega
   change ∑ i∈p,F i= _
   rw [← Finset.add_sum_erase _ F hn, Finset.sum_eq_single_of_mem (n+1) (by simp [p]) (fun j hj hn=>?_)]
   · unfold F; rw [show n+m+1-n=m+1 from by omega,show n+m+1-(n+1)=m from by omega,hf.live,hf.then1,hg.live,hg.then1]
   unfold F; simp [p] at hj; rcases show j<n∧n≤n ∨ n+m+1-j<m from (by omega) with h|h
   · rw [hf.first _ h.1,zero_mul]
   rw [hg.first _ h,mul_zero]
lemma constant (a:ℝ):Glow 0 (fun _=>a) a 0:= ⟨contDiffAt_const,by intros; omega, someJ_zero _,jo_one.trans (deriv_const ..)⟩
lemma nScale (hf: Glow n f a b)(k:ℝ): Glow n (k • f) (k*a) (k*b):= by simpa only [Nat.zero_add,zero_mul, add_zero] using! ((constant k).times hf)
end Glow

section
variable {R : Type*}[CommSemiring R]
def dot [DecidableEq I](f g:I→R)(s:Finset I):R:=∑ i∈s,g i * (∏ j∈s.erase i,f j)
lemma yaw [DecidableEq I](f g:I→R)(s:Finset I)(b:I)(hb:b∉s): dot f g (Insert.insert b s) = f b * dot f g s + g b*(∏ i∈s,f i):= by
   unfold dot; rw [Finset.sum_insert hb,Finset.erase_insert hb,Finset.mul_sum,add_comm]; congr 1; apply Finset.sum_congr rfl; intro i hi
   have he:b≠i:= by intro h; exact hb (h ▸ hi)
   rw [Finset.erase_insert_of_ne he,Finset.prod_insert (fun h=> hb (mem_erase.mp h).2)]; ring
lemma listed [DecidableEq I](f g:I→R)(s:Finset I): dot f g s=∑ i∈s,∏ j ∈ s,(if i=j then g j else f j):= by
   refine Finset.sum_congr rfl fun i hi=> ?_; rw [← Finset.mul_prod_erase _ _ hi, if_pos rfl]; congr 1; exact Finset.prod_congr rfl fun j hj=> (if_neg (Ne.symm (mem_erase.mp hj).1)).symm
variable (φ ψ:I→ℝ)(f:I→ℝ→ℝ)(p:I→ℕ)
lemma Glow.product [DecidableEq I](s:Finset I)(h:∀ i,Glow (p i) (f i) (φ i) (ψ i)) : Glow (∑ i∈s,p i) (∏ i∈s,f i) (∏ i∈s,φ i) (dot φ ψ s):= by
   induction s using Finset.induction_on with
   | empty => simp only [Finset.prod_empty, Finset.sum_empty,dot]; exact Glow.constant 1
   | insert j s hj ih=> rw [Finset.prod_insert hj,Finset.prod_insert hj, Finset.sum_insert hj,yaw φ ψ s j hj]; exact (h j).times ih
end
end YM.PositionX.Jet
