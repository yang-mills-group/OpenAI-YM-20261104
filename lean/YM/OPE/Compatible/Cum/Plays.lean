import YM.OPE.Compatible.Lark.Wide
/-!
# Labeled moment quotient. finite cumulants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter Set MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin
variable {E F I J R:Type} [CommRing R][DecidableEq I]
local notation "P"=> Finset I
abbrev Con (f g:P→R)(s:P):=∑ u∈s.powerset,f u*g (s\u)
private lemma Remaining (s t:P)(h:t∈ s.powerset.erase s):t ⊂ s:=Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_of_mem_erase h),Finset.ne_of_mem_erase h⟩
-- def
protected def Tab (f h:P→R)(s:P) : R:= h s - ∑ u∈(s.powerset.erase s).attach, Shell.Tab f h u.val * f (s \ u.val)
termination_by s.card
decreasing_by
   all_goals exact Finset.card_lt_card (Remaining s _ u.property)
lemma Tab_rec (f h:P→R)(s:P): Shell.Tab f h s=h s-∑ u∈s.powerset.erase s,Shell.Tab f h u*f (s\u):=by rw [Shell.Tab, Finset.sum_attach (s.powerset.erase s) (fun u=>Shell.Tab f h u*f (s\u))]
lemma composite (f h:P→R)(hp:f ∅=1)(s:P):Con (Shell.Tab f h) f s=h s:=by
     unfold Con; rw [←sum_erase_add _ _ (mem_powerset_self _), Finset.sdiff_self,hp,mul_one, Tab_rec f h s]; abel
lemma agrees (q f h:P→R)(hp:f ∅=1)(s:P)(he:∀ j⊆s,Con q f j=h j): q s=Shell.Tab f h s:=by
    induction s using Finset.strongInduction with
    | _ s ih =>
       rw [Tab_rec _ _ s,← he s le_rfl]; unfold Con; rw [← sum_erase_add _ _ (mem_powerset_self _), Finset.sdiff_self,hp,mul_one]; rw [show (∑ u∈s.powerset.erase s, Shell.Tab f h u*f (s\u))=∑ u∈s.powerset.erase s,q u*f (s\u) from Finset.sum_congr rfl (fun i hi=>congr_arg (· * f (s\i)) (ih i (Remaining s i hi) (fun j hj=>he j (hj.trans ((Remaining s i hi).le)))).symm)]; abel
lemma powers_extend (f:P→R)(s:P)(i:I)(hi:i∉s): (∑ u∈(insert i s).powerset, f u)=(∑ u∈s.powerset,f u)+(∑ u∈s.powerset,f (insert i u)):=by
    rw [Finset.powerset_insert]; rw [sum_union,sum_image]; · intro x hx y hy e; have hk:=congr_arg (fun x:P=>x.erase i) e; rw [erase_insert (fun hp=> hi (mem_powerset.mp hx hp)), erase_insert (fun hp=> hi (mem_powerset.mp hy hp))] at hk; exact hk
    refine Finset.disjoint_left.mpr (fun x hx h=>?_); obtain ⟨p,hp,rfl⟩:= mem_image.mp h; exact hi (mem_powerset.mp hx (mem_insert_self ..))
def Push (f:P→R)(i:I)(s:P):R:= if i∈s then f (s.erase i) else 0
lemma pushesT (f g:P→R)(i:I)(s:P): Con (Push f i) g s=Push (Con f g) i s:=by
     by_cases h:i∈s; swap
     · rw [Push,if_neg h]; exact sum_eq_zero (fun k hk=>by rw [Push, if_neg (fun hi=>h ((mem_powerset.mp hk) hi)),zero_mul])
     rw [Push, if_pos h]; let S:= s.erase i; change Con _ _ s=Con _ _ S; rw [show s=insert i S from (Finset.insert_erase h).symm]; unfold Con; rw [powers_extend (s:=S) _ _ (Finset.notMem_erase i s)]; have he(u:P)(h:u∈ S.powerset):i ∉ u:=fun hp=> Finset.notMem_erase i s (mem_powerset.mp h hp)
     rw [sum_eq_zero (f:=fun x=>Push f i x*g ((insert i S)\x)) (s:=S.powerset), zero_add]; apply sum_congr rfl; intro u hu; rw [Push, if_pos (mem_insert_self ..),erase_insert (he u hu)]; congr 2; ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; have hh:=Finset.notMem_erase i s; change i ∉ S at hh; by_cases hv:x=i <;>simp [*]
     intro x hx; rw [Push,if_neg (he x hx),zero_mul]
lemma roses (F:I→P→R)(g:P→R)(t:P): Con (fun u=>∑ i ∈ u,F i (u.erase i)) g t= ∑ i∈t,Con (F i) g (t.erase i):=by
     calc
        _=∑ i∈t,Con (Push (F i) i) g t:=by
           unfold Con; rw [sum_comm]; apply sum_congr rfl; intro u hu; rw [← Finset.sum_mul]; congr 1; refine Eq.trans ?_ (sum_subset (mem_powerset.mp hu) (fun j _ hp=>?_) ) -- orientation
           · exact sum_congr rfl fun i h=>by simp only [Push,if_pos h]
           simp only [Push,if_neg hp]
        _= _:= Finset.sum_congr rfl fun i hi=>by rw [pushesT,Push,if_pos hi]
end YM.OPE.Libra.Shell
