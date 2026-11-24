import YM.SchemeRG11.Flock.Bern
/-! Unoriented calculus, finite tensor symbols. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Flock
open Function Lattice
variable {I:Type*}[DecidableEq I]
abbrev Bag:=Finset I
def batch (s:Finset I)(r:I→Axis):Fliers:=∑ i∈s,{r i}
lemma batch_insert(i:I)(s:Finset I)(h:i∉s)(r:I→Axis):batch (insert i s) r=r i ::ₘ batch s r:=by rw [batch,Finset.sum_insert h]; rfl -- singleton_add?
def clutch {j:ℕ}(r:Fin j→ Axis):Fliers:= batch Finset.univ r
lemma cargo {j:ℕ}(r:Fin j→Axis): (clutch r).card=j:=by
 unfold clutch batch
 -- map sum
 have H (s:Finset (Fin j)):(batch s r).card=s.card:=by induction s using Finset.induction_on with | empty=>simp [batch] | insert i s h ih=>rw [batch_insert _ _ _ _, Multiset.card_cons, Finset.card_insert_of_notMem h,ih]; exact h
 rw [show ∑ i,_= batch Finset.univ r from rfl,H]; simp
lemma resort {j:ℕ}(r:Fin j→Axis)(s:Equiv.Perm (Fin j)):clutch (r ∘ s)=clutch r:= Equiv.sum_comp s (fun i=>({r i}:Fliers))
lemma tract {j:ℕ}(r:Fin j→Axis)(i:Axis):clutch (Fin.cons i r)=i ::ₘ clutch r:=by unfold clutch batch; rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ];rfl
lemma gather {j:ℕ}(s:Fliers)(h:s.card=j):∃r:Fin j→Axis,clutch r=s:=by
 induction j generalizing s with
 | zero=> refine ⟨Fin.elim0, Multiset.card_eq_zero.mp (cargo _) |>.trans (Multiset.card_eq_zero.mp h).symm⟩
 | succ j ih=>
   induction s using Multiset.induction with
   | empty=>simp at h
   | cons i s =>obtain ⟨r,rfl⟩:= ih s (by simpa using h); exact ⟨_,tract r i⟩

section add
variable {E:Type*}[AddCommGroup E][Module ℝ E]
lemma flocksum (r:I→Axis)(s:Finset I)(f:Plane E)(x:Cover): fleet (batch s r) f x=∑ t∈s.powerset,(-1:ℝ)^(s.card-t.card) • f (x+∑ i∈t,step (r i)):=by
 induction s using Finset.induction_on generalizing x with
 | empty=> rw [batch,Finset.sum_empty,fleet_zero]; simp
 | insert i s hi ih=>
    rw [batch_insert _ _ hi,fleet_cons]; change soar (r i) _ _=_; rw [soar_apply,ih,ih,Finset.powerset_insert,Finset.sum_union,Finset.sum_image,sub_eq_add_neg]; conv_rhs=>rw [add_comm]
    · congr 1
      · apply Finset.sum_congr rfl; intro t ht
        have h:i∉t:=fun H=> hi (Finset.mem_powerset.mp ht H)
        rw [Finset.card_insert_of_notMem h, Finset.card_insert_of_notMem hi, Finset.sum_insert h,Nat.add_sub_add_right,←add_assoc]
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro t ht
      have h:=Finset.card_le_card (Finset.mem_powerset.mp ht); rw [Finset.card_insert_of_notMem hi, show s.card+1-t.card=s.card-t.card+1 by omega,pow_add]; simp
    · intro a ha b hb e; rw [← Finset.erase_insert (show i∉a from fun h=>hi (Finset.mem_powerset.mp ha h)), e,Finset.erase_insert (show i∉b from fun h=>hi (Finset.mem_powerset.mp hb h))]
    exact Finset.disjoint_left.mpr fun t h₁ h₂=> by obtain ⟨v,_,e⟩ :=Finset.mem_image.mp h₂; exact hi (Finset.mem_powerset.mp h₁ (by rw [←e]; simp))
lemma clutch_eq {j:ℕ}(r:Fin j→Axis)(f:Plane E)(x:Cover): fleet (clutch r) f x=∑ t:Finset (Fin j),Pert.Bare.sign t • f (x+∑i∈t,step (r i)):=by rw [clutch,flocksum,Finset.card_univ,Fintype.card_fin];simp [Pert.Bare.sign_eq]
end add
open ContinuousMultilinearMap Tensor
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]
def printT (n:ℕ)(b:Fliers→ F): T E4 F n:=∑ v: Fin n→Axis,Pert.Bare.spaceMon v (b (clutch v))
lemma print_tip(n:ℕ)(b:Fliers→ F)(v: Fin n→Axis): printT n b (basis ∘ v)=b (clutch v):=by
 rw [printT,sum_apply, Finset.sum_eq_single v]; unfold comp; rw [Pert.Bare.mon_eq]; simp
 · intro i hi he; rw [Pert.Bare.mon_eq]; obtain ⟨k,hk⟩ :=Function.ne_iff.mp he
   rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk]),zero_smul]
 simp
lemma tipped {n:ℕ}(A B:T E4 F n)(h:∀v:Fin n→Axis,A (basis ∘ v)=B (basis ∘ v)): A=B:=by
 ext1 z
 have hm i: ∑ l:Axis,z i l • basis l=z i:=by ext1 i; simp [WithLp.ofLp_sum, Finset.sum_apply,basis,Pi.single_apply, mul_ite]
 rw [←funext hm]; change A.toMultilinearMap _= B.toMultilinearMap _; rw [MultilinearMap.map_sum_finset,MultilinearMap.map_sum_finset]; apply Finset.sum_congr rfl; intro a _; rw [A.toMultilinearMap.map_smul_univ,B.toMultilinearMap.map_smul_univ]; exact congrArg (fun y=>(∏ i:Fin n,z i (a i)) • y) (h a) -- syntax
lemma print_sym(n:ℕ)(b:Fliers→ F): Tensor.Sym (printT n b):=by
 intro v s
 let A:=printT n b
 have h : A.domDomCongr s=A:=by -- check inverse
   refine tipped _ _ ?_; intro r
   rw [domDomCongr_apply]; change printT n b (basis ∘ (r ∘ s)) = _; rw [print_tip,resort]; exact (print_tip ..).symm
 exact DFunLike.congr_fun h v
lemma front(n:ℕ)(b:Fliers→F)(v:Fin n→ Axis)(i:Axis) : (printT (n+1) b).curryLeft (basis i) (basis ∘ v)= b (i ::ₘ clutch v):=by
 rw [curryLeft_apply]; rw [show Fin.cons (basis i) (basis ∘ v)=basis ∘ (Fin.cons i v) from funext (fun k=>Fin.cases (by simp) (fun i=>by simp) k), print_tip,tract]
end YM.SchemeRG11.Flock
