import YM.OPE.Yarn.Aider
/-!
# A scheduling layout built by ordering distances (leaves of the term only)

Projection paths: every active slot keeps one leaf of the original sources
as center, reaps all others. No comparison of different independent cluster
ratios. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Finset Function Filter Set Lattice
open scoped Topology BigOperators Classical
variable {I J : Type}[Fintype I][DecidableEq I]
-- fix bij-val ranking explicitly bounded; easier sorting on finset. finite family.
structure Mast (I:Type)[Fintype I] where
   rank : I→ Fin (Fintype.card I)
   inj : Injective rank
   root : I
   high a: rank a ≤ rank root
   parent : I→ I
   grows i : i≠root → rank i < rank (parent i)
   sure : parent root=root
instance : Finite (Mast I):= by
   refine Finite.of_injective (fun v:Mast I=>(v.rank,v.root,v.parent)) ?_
   rintro ⟨_,_,_,_,_,_,_⟩ ⟨_,_,_,_,_,_,_⟩ he; simp only [Prod.mk.injEq] at he; obtain ⟨rfl,rfl,rfl⟩:=he;rfl
namespace Mast
variable (η:Mast I)
structure Cluster (F:I→ I→ℝ) : Prop where
   least i:i≠η.root→ ∀ j k,j≠k→ η.rank i ≤ η.rank j → η.rank i ≤ η.rank k → F i (η.parent i)≤F j k
private def Minimum (u : Finset I) (x:I)(F:I→I→ℝ) (p:I→ℕ)(v:I→I): Prop:= ∀ i∈u,i≠x→ (p i<p (v i) ∧ v i∈u) ∧ ∀ j∈u,∀ k∈u,k≠j→ p i≤ p k→ p i≤ p j→ F i (v i) ≤ F k j
omit [Fintype I] in
private lemma projected (x:I)(F:I→I→ℝ) (hF:∀ i j,F i j=F j i) (u:Finset I)(he:x∈u) : ∃ p:I→ℕ,∃ l:I→I, Set.InjOn p ↑u ∧ p x+1=u.card ∧ (∀ i∈u,p i ≤ p x) ∧ l x=x ∧ Minimum u x F p l:= by
   induction u using Finset.strongInductionOn
   rename_i u ih
   let s:= (u ×ˢ u).filter fun k=> k.1 ≠ k.2 ∧ k.1≠x
   cases s.eq_empty_or_nonempty with
   | inl h=>
      have ht: u={x}:= by apply Finset.eq_singleton_iff_unique_mem.mpr ⟨he,?_⟩; intro i hi; by_contra hx; exact notMem_empty (i,x) (h ▸ (show (i,x)∈s from mem_filter.mpr ⟨mem_product.mpr ⟨hi,he⟩,hx,hx⟩))
      rw [ht,Finset.card_singleton]; refine ⟨0,id,(by simp),rfl,by simp,rfl,fun i hi hz=>(hz (mem_singleton.mp hi)).elim⟩
   | inr h=>
      obtain ⟨⟨i,j⟩,hq,hp⟩:= Finset.exists_min_image s (fun k=>F k.1 k.2) h; obtain ⟨hq,h,hz⟩:=mem_filter.mp hq; obtain ⟨hi,hj⟩:=mem_product.mp hq; let y:= u.erase i; have hY:x∈y:= mem_erase.mpr ⟨hz.symm,he⟩; have he':j∈y:= mem_erase.mpr ⟨h.symm,hj⟩
      have hV (a:I):a∈u ↔ a=i ∨ a∈y:=by nth_rw 1 [← Finset.insert_erase hi]; exact Finset.mem_insert
      have ha (u' v)(hp':u'∈u)(hh':v∈u)(h:u' ≠ v): F i j ≤ F u' v:=by
         by_cases hx:u'=x; subst u'; rw [hF x]; exact hp (v,x) (mem_filter.mpr ⟨mem_product.mpr ⟨hh',he⟩,h.symm,h.symm⟩)
         exact hp (u',v) (mem_filter.mpr ⟨mem_product.mpr ⟨hp',hh'⟩,h,hx⟩)
      obtain ⟨k,v,hx,hb,hw,hX,hQ⟩:=ih y (Finset.erase_ssubset hi) hY; let v':=Function.update v i j; let k':= Function.update (fun i=> k i+1) i 0
      have hm(i')(hp:i'∈y):k' i'=k i'+1:= Function.update_of_ne (mem_erase.mp hp).1 ..; have hn(i')(hp:i'∈y):v' i'=v i':= Function.update_of_ne (mem_erase.mp hp).1 ..; have h0:k' i=0:= Function.update_self ..; have hy(a)(he:a∈y):k' i<k' a:= by rw [h0,hm a he]; omega
      have hp {i j} (hx:i∈y)(he:j∈y): k' i ≤ k' j ↔ k i ≤ k j:= by simp only [hm i hx,hm j he, Nat.add_le_add_iff_right]
      refine ⟨k', v', ?_, ?_, ?_, (hn _ hY).trans hX, ?_⟩
      · rintro a ha b hb he; rcases (hV _).1 ha with h| h
        · subst a; rcases (hV _).1 hb with hb|hb; exact hb.symm; exact ((hy b hb).ne he).elim
        rcases (hV _).1 hb with he'| hb; subst b; exact ((hy a h).ne he.symm).elim
        exact hx h hb (le_antisymm ((hp h hb).1 he.le) ((hp hb h).1 he.ge))
      · rw [hm _ hY,hb]; exact Finset.card_erase_add_one hi
      · intro a he; rcases (hV a).1 he with he|he; exact he.symm ▸ (hy x hY).le; exact (hp he hY).2 (hw _ he)
      intro a hA hz; rcases (hV _).1 hA with hA|hA
      · subst a; rw [show v' i=j from Function.update_self ..]; exact ⟨⟨hy j he',hj⟩,fun k hk j hj h _ _=>ha j k hj hk h⟩
      obtain ⟨⟨hq,hΩ⟩,hQ'⟩:= hQ a hA hz; have he(k)(hk:k∈u)(hp:k' a ≤ k' k): k∈y:= by rcases (hV _).1 hk with h|h; rw [h] at hp; exact ((hy a hA).not_ge hp).elim; exact h
      rw [hn _ hA]; refine ⟨⟨?_,(Finset.erase_subset ..) hΩ⟩,fun j hj k hk' h hh hx=> hQ' _ (he _ hj hx) _ (he _ hk' hh) h ((hp hA (he _ hk' hh)).1 hh) ((hp hA (he _ hj hx)).1 hx)⟩
      rw [hm _ hA,hm _ hΩ]; exact Nat.succ_lt_succ hq
lemma select (x:I)(F:I→I→ℝ) (hF:∀ i j,F i j=F j i): ∃ η:Mast I,η.root=x ∧ η.Cluster F:=by
   obtain ⟨p,v,ht,hb,h,H,hQ⟩:= projected x F hF Finset.univ (mem_univ _)
   rw [card_univ] at hb; let f (i:I) : Fin (Fintype.card I):= ⟨p i,(h i (mem_univ _)).trans_lt (hb ▸ (Nat.lt_add_one _))⟩
   let q:Mast I:=⟨f,fun i hi hx=> ht (mem_univ _) (mem_univ _) (congr_arg Fin.val hx),x,fun i=>h i (mem_univ _),v,fun i hi=>(hQ i (mem_univ _) hi).1.1,H⟩
   exact ⟨q,rfl,⟨fun i hi j k hj hk hn=> (hQ i (mem_univ _) hi).2 k (mem_univ _) j (mem_univ _) hj hk hn⟩⟩
lemma eventually_select {φ:Ultrafilter J}(x:I)(F:J→I→I→ℝ)(h:∀ j a b,F j a b=F j b a) : ∃ η:Mast I, η.root=x ∧ ∀ᶠ k in (φ:Filter J), η.Cluster (F k):=by
   obtain ⟨η,hη⟩:= (Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall (fun k=> select x (F k) (h k)) : ∀ᶠ k in (φ:Filter J),∃ η : Mast I,η.root=x∧ η.Cluster (F k))); exact ⟨η,hη.exists.choose_spec.1,hη.mono fun i hi=>hi.2⟩
end Mast
end YM.OPE.Yarn

