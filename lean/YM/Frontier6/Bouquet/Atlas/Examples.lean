import YM.Frontier6.Bouquet.Atlas.Burst

/-! Choose true-equality groups in a normalized **annulus**. This is for a
 bounded partition-of-unity argument; no countably many solution-dependent
 angular limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q: Ensemble}(v: Slot → E4)(p:Pod)
section
private def club (i:p.val) : Pod:= ⟨p.val.filter fun j=>v j=v i, i,Finset.mem_filter.mpr ⟨i.property,rfl⟩⟩
private def college : Ensemble where
    choose:= Finset.univ.image (club v p)
    pairwise:= by
       intro i hi j hj he; obtain ⟨i,h,rfl⟩:= Finset.mem_image.mp hi; obtain ⟨j,h,rfl⟩:= Finset.mem_image.mp hj
       refine Finset.disjoint_left.mpr (fun k hk hv=> he (Subtype.ext ?_)); have hz:v i=v j:= ((Finset.mem_filter.mp hk).2).symm.trans (Finset.mem_filter.mp hv).2; change p.val.filter _=p.val.filter _; rw [hz]
private lemma college_le : college v p ≤ only p:=by
    have h(i:Pod)(he:i∈(college v p).choose): i≤p:=by obtain ⟨j,_,rfl⟩:= Finset.mem_image.mp he; exact Finset.filter_subset ..
    constructor; rw [along_only]; ext1 i; rw [mem_along]; constructor; rintro ⟨j,hj,H⟩; exact h _ hj H
    intro hi; let q: p.val:=⟨i,hi⟩; refine ⟨club v p q,Finset.mem_image_of_mem _ (Finset.mem_univ q), Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
    exact fun i hi=> ⟨_,Finset.mem_singleton_self p,h _ hi⟩
private lemma tapes {i:Pod}(hi:i∈(college v p).choose){a b:Slot}(hh:a∈i.val)(hv:b∈ i.val): v a=v b:= by obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hi; exact ((Finset.mem_filter.mp hh).2).trans ((Finset.mem_filter.mp hv).2).symm
private lemma colleges {i:Pod}(hi:i∈(college v p).choose){a b:Slot}(hh:a∈i.val)(hv:b∈p.val)(h:v a=v b): b∈ i.val:=by obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hi; exact Finset.mem_filter.mpr ⟨hv,h.symm.trans (Finset.mem_filter.mp hh).2⟩
lemma clique (hh:¬∀ i∈p.val,v i=v p.here) : ∃ Q:Ensemble,Q ≤ only p ∧ p∉Q.choose ∧
    (∀ (i:Q)(a:Slot), a∈i.val.val→ v a=v i.val.here) ∧ Injective (fun i:Q=> v i.val.here):=by
    let Q:= college v p; have hv:= college_le v p; refine ⟨Q, hv, fun h=>hh (fun i hi=>tapes v p h hi p.here_mem), fun i a h=>tapes v p i.property h i.val.here_mem,?_⟩ -- h hp fill
    intro i j he; have hh:j.val≤p:= by obtain ⟨v,hv,h⟩:=hv.2 j j.property; exact only_mem.mp hv ▸ h
    exact serial Q (colleges v p i.property i.val.here_mem (hh j.val.here_mem) he) j.val.here_mem
end

variable (i:P)
lemma contestants (x: normal i.val)(hx:x≠0): ∃ (Q : Ensemble)(h:Burst i Q),
   (∀ j∈dialogues h.le i,∀ a∈j.val.val, house a x.val=house j.val.here x.val) ∧ Set.InjOn (fun j:Q=> house j.val.here x.val) (dialogues h.le i:Set Q):=by
   let r:= i.val; let F(j:Slot):=house j x.val
   have he:= college_le F i.val; obtain ⟨Q,g,hp,hC,hF⟩:=clique F r (fun hh=> hx (by
       have hv: x.val=0:= (Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint (normal i.val)) x.val x.property (tie_up x.val hh)) -- inspect
       exact Subtype.ext hv))
   let W:= P.except r
   let h:=except_free P i.property; let hv:= Free.refines h g (le_refl W); let Y:=merge hv; have hk:Y≤P:= except_eq P i.property ▸ merge_le h g (le_refl W)
   have hz:Burst i Y:=⟨hk, fun hp'=> (Finset.mem_union.mp hp').elim hp (fun hc=>Finset.notMem_erase _ _ hc), fun j hj=> Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun h=> hj (Subtype.ext h),j.property⟩)⟩
   have hs(j:Y)(hh:j∈dialogues hz.le i) : ∃ a:Q,j=germL hv a:=by
       obtain ⟨a|a,rfl⟩:= (parts hv).surjective j; exact ⟨a,rfl⟩
       have ht:= (members' ..).mp hh; obtain ⟨h,hP⟩:= Finset.mem_erase.mp a.property; exact False.elim (h (same hP i.property a.val.here_mem (ht a.val.here_mem)))
   refine ⟨Y,hz,fun j hj=>?_,?_⟩; obtain ⟨a,rfl⟩:= hs j hj; exact fun i hi=> hC a _ hi
   intro j hj k hk h; obtain ⟨a,rfl⟩:= hs j hj; obtain ⟨b,rfl⟩:= hs k hk; exact congr_arg _ (hF h)
end YM.Frontier6.Bouquet.Atelier
