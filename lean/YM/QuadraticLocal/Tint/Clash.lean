import YM.Marker.Weight
/-! # qlocal: in particular reject any repeated mark in concatenations in the log. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tint
open Function Filter Finset Marker
open scoped Topology Classical BigOperators
variable {V α β ι : Type*}[DecidableEq V]{R:Marker.Census V}
namespace Clash
variable (f:ι→R.Mode)(g:ι→ℂ)(S:Finset ι)
variable {v w u:R.Mode}
def apart:= Set.Pairwise (↑S) (fun i j=> Disjoint (f i).val (f j).val)
def issued := S.biUnion (fun i=>(f i).val)
def beacon : Poly R:= ∏ i∈S,Poly.send (f i) (g i)
def lit : Prop := ∃ p:R.Mode,p≠ R.quiet ∧ (beacon f g S|>.part p) ≠ 0
private lemma carted (hv:Poly.merges u v w) (i j:ℂ): Poly.send u i*Poly.send v j=Poly.send w (i*j):=by
   ext k; rw [show ((Poly.send u i*Poly.send v j).part k)=_ from Poly.cart ..,Poly.part_send]; by_cases he:k=w; subst k; · simp only [if_true,if_pos hv]
   rw [if_neg he,if_neg (fun q : Poly.merges u v k=> he (Subtype.ext (q.2.symm.trans hv.2)))]
private lemma clash (hp:(beacon f g S).part v ≠0) : (apart f S) ∧ issued f S=v.val:= by
 induction S using Finset.induction generalizing v with
 | empty=>
   have he : (beacon f g ∅)=1:= prod_empty; have h:v=R.quiet:=by contrapose! hp; rw [he,Poly.one_part,if_neg hp];
   exact ⟨by intro i hi; simp at hi, by simp [issued,h,Census.quiet]⟩
 | insert i S hi IH=>
   let u:R.Mode:= f i; rw [beacon,prod_insert hi,Poly.part_mul] at hp;
   obtain ⟨j,hj,h⟩:= Finset.exists_ne_zero_of_sum_ne_zero hp; obtain ⟨k,hk,hZ⟩:= Finset.exists_ne_zero_of_sum_ne_zero h; rw [Poly.part_send] at hZ; split_ifs at hZ with ht hQ
   swap; · rw [zero_mul] at hZ; contradiction
   subst j; obtain ⟨hg,hv⟩:= IH (v:=k) (right_ne_zero_of_mul hZ); refine ⟨?_,?_⟩
   · have h(j)(hj:j∈S):Disjoint u.val (f j).val:= ht.1.mono_right (hv ▸ Finset.subset_biUnion_of_mem (fun i=> (f i).val) hj)
     intro j hj k hk he; rcases mem_insert.mp hj with rfl|h₁; exact h _ ((Finset.mem_insert.mp hk).resolve_left he.symm); rcases mem_insert.mp hk with rfl|hq; exact (h j h₁).symm; exact hg h₁ hq he
   unfold issued at hv ⊢; rw [biUnion_insert, ← ht.2,hv]; -- syntax
   contradiction
lemma glows (h:apart f S)(he:issued f S=v.val): beacon f g S=Poly.send v (∏ i∈S,g i):=by
 induction S using Finset.induction generalizing v with
 | empty=> rw [beacon,prod_empty,prod_empty,show v=R.quiet from Subtype.ext (he.symm.trans Finset.biUnion_empty)]; rfl
 | insert i S hi IH=>
   have hp:(f i).val ∪ (issued f S)=v.val:=by rw [← he]; unfold issued; rw [biUnion_insert]
   let v':R.Mode:= ⟨issued f S,R.down v.prop (issued f S) (hp ▸ Finset.subset_union_right)⟩
   have he' j (hj:j∈ S) : Disjoint (f i).val (f j).val:= h (mem_insert_self ..) (mem_insert_of_mem hj) (by rintro rfl; contradiction); rw [show beacon f g (insert i S)= Poly.send (f i) (g i)* beacon f g S from prod_insert hi,prod_insert hi,IH (v:=v') (h.mono (show (S:Set ι) ⊆ _ from fun i hi=> mem_insert_of_mem hi)) rfl]; apply carted; exact ⟨Finset.disjoint_left.mpr (by rintro x hx he; obtain ⟨j,hj,hZ⟩:= Finset.mem_biUnion.mp he; exact Finset.disjoint_left.mp (he' _ hj) hx hZ),hp⟩
lemma permits (hp:(beacon f g S).part v ≠0)(he:v≠R.quiet) : (apart f S)∧ issued f S=v.val∧ S.Nonempty:=by
   obtain ⟨ht,hL⟩:= clash f g S hp; exact ⟨ht,hL,Finset.nonempty_iff_ne_empty.mpr fun hS=> he (Subtype.ext (hL.symm.trans (hS ▸ Finset.biUnion_empty)))⟩
end Clash
end YM.QuadraticLocal.Tint
