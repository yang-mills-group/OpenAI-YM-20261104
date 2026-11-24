import YM.SchemeRG11.Flock.Cairn
/-! Exact Peano and Poisson. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Flock
open Function Lattice
variable {E F:Type*} [AddCommGroup E][AddCommGroup F][Module ℝ E][Module ℝ F]
def bin (x:ℤ)(n:ℕ): ℝ:=match n with
 | 0=>1
 | k+1=>(x-k)/(k+1:ℝ)*bin x k
lemma bin_rise (x:ℤ)(n:ℕ): bin (x+1) (n+1)-bin x (n+1)=bin x n:=by
 induction n with
 | zero=> simp [bin]
 | succ n ih=>
   rw [bin.eq_2, bin.eq_2 x,sub_eq_iff_eq_add.mp ih,bin.eq_2 x]; push_cast
   field_simp
   ring
def pas (t:Fliers):Plane ℝ:=fun x=> ∏i:Axis,bin (x i) (t.count i)
lemma one_leg (i:Axis)(s:Fliers): soar i (pas (i ::ₘ s))=pas s:=by
 funext x; rw [soar_apply]; simp only [pas]
 rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ (Finset.mem_univ i) (f:=fun j=> bin (x j) ((i ::ₘ s).count j)), ←Finset.mul_prod_erase _ (Finset.mem_univ i) (f:=fun j=>bin (x j) (s.count j))]
 -- same products
 let X:= Finset.univ.erase i
 let p:= (∏ j ∈ X, bin (x j) (s.count j))
 have he:(∏ j∈X,bin ((x+step i:Cover) j) ((i ::ₘ s).count j))=p:= Finset.prod_congr rfl fun j h=>by simp [Ne.symm ((Finset.mem_erase.mp h).1.symm)]
 have hz:(∏ j∈X,bin (x j) ((i ::ₘ s).count j))=p:=Finset.prod_congr rfl fun j h=>by simp [show j≠i from (Finset.mem_erase.mp h).1]
 rw [he,hz,← sub_mul]; congr 1; simpa using bin_rise (x i) (s.count i)
lemma no_leg (i:Axis)(s:Fliers)(h:i∉s): soar i (pas s)=0:=by
 funext x; rw [soar_apply]; change _-_=0
 refine sub_eq_zero.mpr (Finset.prod_congr rfl ?_); intro j hj
 rcases eq_or_ne i j with H|H
 · subst j; rw [Multiset.count_eq_zero.mpr h]; rfl
 simp [H.symm]
lemma stalk(t:Fliers):pas t∈ cap ℝ (t.card+1):=by
 induction n:t.card using Nat.strong_induction_on generalizing t with | h n ih=>
 intro s hs
 induction s using Multiset.induction with
 | empty=>simp at hs
 | cons i s w=>
    rw [fleet_cons']; change fleet s (soar i _) =_
    by_cases he:i∈t
    · obtain ⟨a,ha⟩ :=Multiset.exists_cons_of_mem he; subst t; rw [one_leg]; exact member.mp (ih _ (by simp at n; omega) a rfl) _ (by simp at hs n; omega)
    rw [no_leg i t he,map_zero]
lemma mono_test {s t:Fliers}(h:s.card=t.card):fleet s (pas t)=if s=t then (1:Plane ℝ) else 0:=by
 induction s using Multiset.induction generalizing t with
 | empty=> have hh:t=0:=Multiset.card_eq_zero.mp h.symm; subst t; change pas 0=_; ext; simp [pas,bin]
 | cons i s ih=>
    rw [fleet_cons']; change fleet s (soar i _) =_
    by_cases ht:i∈t
    · obtain ⟨v,H⟩ :=Multiset.exists_cons_of_mem ht; subst t; rw [one_leg,ih (by simpa using h)]; simp
    rw [no_leg i t ht,map_zero, if_neg fun w=> ht (by rw [←w]; simp)]
lemma mule(v:E)(f:Plane ℝ)(s:Fliers) : fleet s (fun x=> f x • v)=fun x=> fleet s f x • v:=plane_map ((LinearMap.id:Module.End ℝ ℝ).smulRight v) f s
lemma peano (n:ℕ)(b:Fliers→E):∃ p:Plane E,p∈ cap E (n+1)∧∀t:Fliers,t.card=n→fleet t p 0=b t:=by
 let u (s:Sym Axis n):Plane E:=fun x=> pas s.val x • b s.val
 refine ⟨∑ s,u s,?_,fun t ht => ?_⟩
 · apply Submodule.sum_mem; intro s hs a h; rw [show u s=_ from rfl,mule]; funext x; rw [member.mp (stalk _) _ (by rw [s.property]; exact h)]; exact zero_smul _ _
 rw [_root_.map_sum,Finset.sum_apply]; classical
 rw [Finset.sum_eq_single (s:=Finset.univ (α:=Sym Axis n)) (f:=fun v:Sym Axis n=>fleet t (u v) 0) (⟨t,ht⟩:Sym Axis n)]; unfold u; rw [mule]; simp [mono_test rfl]
 · intro b hab hn; unfold u; rw [mule,mono_test (ht.trans b.property.symm), if_neg (show t≠b.val from fun h=>hn (Subtype.ext h.symm))]; apply zero_smul ℝ
 simp

end YM.SchemeRG11.Flock
