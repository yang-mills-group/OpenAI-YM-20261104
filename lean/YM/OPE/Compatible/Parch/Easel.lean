import YM.OPE.Compatible.Parch.Garden
/-!
# Height dividend in one layer. Difference at zero-field amplitude.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {i j r d m k l:ℕ}
section
variable {X E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "I!"=>Fin (r+1)
namespace FoldU
-- hi indices less are x; last=size
noncomputable def rowP (x y:E)(s:ℕ): I!→ E:=fun i=> if i.val<s then x else y
noncomputable def banner (x y:E)(a:I!):I!→ E:=rowP x y a.val
lemma panorama (T:Tensor.T E ℝ (r+1))(x y:E): diagonal T x-diagonal T y=∑ i:I!,T (update (banner x y i) i (x-y)):=by
        let F(i:ℕ):ℝ:= T (rowP x y i); have h(i:I!) : T (update (banner x y i) i (x-y))=F (i.val+1)- F i.val:=by
              rw [show T (update (banner x y i) i (x-y))= T (update (banner x y i) i x)- T (update (banner x y i) i y) from ?_]; swap; · rw [sub_eq_add_neg,T.map_update_add]; erw [T.map_update_neg]; abel -- rfl?
              apply congr_arg₂
              · apply congr_arg; funext j; by_cases ht:j=i; · subst j; rw [update_self,rowP,if_pos (Nat.lt_succ_self _)];
                unfold banner rowP; rw [update_of_ne ht]; have hz:j.val≠i.val:=fun h=>ht (Fin.ext h); split_ifs<;>first| rfl| omega
              apply congr_arg; funext j; by_cases ht:j=i; · subst i; simp only [banner,rowP,lt_self_iff_false,ite_false, update_self]
              rw[update_of_ne ht]; rfl
        simp_rw [h]; rw [Fin.sum_univ_eq_sum_range (fun i=>F (i+1)-F i),sum_range_sub]; exact congr_arg₂ (·-·) (congr_arg T (funext fun i=> (if_pos i.isLt).symm)) (congr_arg T (funext fun i=> (if_neg i.val.not_lt_zero).symm)) -- named lemma
variable {P:Tensor.T E ℝ (r+1)}
noncomputable def tab (x y:E)(i:I!)(z:E):Fin (r+1)→ E:=update (banner x y i) i z
noncomputable def pop (P:T E ℝ (r+1))(x y:E):E→ₗ[ℝ]ℝ:={
     toFun z:= ∑ i:I!,P (tab x y i z)
     map_add' a b:=by unfold tab; rw[←Finset.sum_add_distrib]; exact sum_congr rfl fun i _=> P.map_update_add ..
     map_smul' c z:=by unfold tab; rw[RingHom.id_apply, Finset.smul_sum]; exact sum_congr rfl fun i _=> P.map_update_smul ..
}
lemma popularity (x y:E): diagonal P x-diagonal P y=pop P x y (x-y):= panorama ..
lemma tab_r (x y z:E)(i:I!)(t:ℝ): P (tab (t • x) (t • y) i z)= t^r * P (tab x y i z):=by
       let A(j:I!):ℝ:=if j=i then 1 else t; have he : tab (t • x) (t • y) i z=(fun j=> A j • tab x y i z j):=by
             unfold tab; funext j; by_cases hp:j=i; subst j; rw [update_self,update_self,show A i=1 from if_pos rfl,one_smul]; rw [update_of_ne hp,update_of_ne hp,show A j=t from if_neg hp]; unfold banner rowP;split<;>rfl
       rw [he,P.map_smul_univ A,← Finset.prod_erase_mul (Finset.univ:Finset I!) _ (mem_univ i)]; rw [show A i=1 from if_pos rfl,mul_one]; let V:=univ.erase i; rw [show (∏ j∈V,A j)=t^r from (Finset.prod_congr rfl (fun j (hj:j∈V)=> (show A j=t from if_neg (mem_erase.mp hj).1))).trans (by simp[V])]; rfl -- API
lemma popC (P:T E ℝ (r+1))(x y:E)(t:ℝ): pop P (t•x) (t•y)= t^r • pop P x y:=LinearMap.ext fun u=>by change (∑ i,P (tab _ _ i u))= t^r*(∑ i,P (tab x y i u));rw [mul_sum]; exact sum_congr rfl fun _ _=>tab_r ..
lemma pol_s (P:T E ℝ (r+1))(M:E→L[ℝ] E)(x:E):ContDiff ℝ ω (fun y=> (pop P y (M y)) x):=by
       change ContDiff _ _ (fun y=>∑ i,P (tab y _ i x)); apply ContDiff.sum; intro i _; apply P.contDiff.comp; refine contDiff_pi.mpr (fun j=>?_) ; by_cases h:j=i; · subst j; simpa only[tab,update_self] using (contDiff_const (c:=x)) -- unif
       simp only[tab, update_of_ne h,banner,rowP]; split <;> first|exact contDiff_id| exact M.contDiff
end FoldU
end
end YM.OPE.Claw
