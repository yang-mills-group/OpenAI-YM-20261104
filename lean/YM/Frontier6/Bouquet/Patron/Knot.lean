import YM.Frontier6.Bouquet.Patron.Gentry
import YM.Frontier6.Bouquet.Ensemble.Twine

/-! Partially applying to disjoint groups. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{S:Table C.book}{P Q R U: Ensemble}
variable (h:Free P Q)(i:P)(j:Q) {Y:Type*}[AddCommGroup Y][Module ℂ Y]
-- commute Sum orientation for currying with respect to Q
def heli : merge h ≃ Q ⊕ P := (parts h).symm.trans (Equiv.sumComm ..)
theorem heli_left : heli h (germL h i)=Sum.inr i := by rw [heli, show germL h i= parts h (Sum.inl i) from rfl]; simp
theorem heli_right : heli h (germR h j)= Sum.inl j:= by rw [heli,show germR h j= parts h (Sum.inr j) from rfl]; simp
section
variable (P Q : Ensemble)
end
def joinP (u:Program S P)(v:Program S Q)(w:merge h) := Sum.elim v u (heli h w)
def courser (F:Patron S (merge h) Y) : Patron S Q (Patron S P Y):= MultilinearMap.currySum (F.domDomCongr (heli h))
def follow (F: Patron S (merge h) Y)(v:Program S Q): Patron S P Y:= courser h F v
lemma follow_at (F: Patron S (merge h) Y) (u:Program S P)(v:Program S Q): follow h F v u=F (joinP h u v):=rfl
lemma hear_mix (f:Program S (merge h)): joinP h (f ∘ germL h) (f ∘ germR h)=f:=by ext1 i; obtain ⟨i|i,rfl⟩:= (parts h).surjective i; change Sum.elim _ _ (heli h (germL h i))=(f ∘ germL h) i; rw [heli_left];rfl; change Sum.elim _ _ (heli h (germR h i))=_; rw [heli_right];rfl
section
variable (F:Patron S (merge h) Y)(A: Program S Q)(B:Spelling S →ₗ[ℂ] Spelling S)
lemma transactions_left : follow h (transaction F (germL h i) B) A= transaction (follow h F A) i B:=by
    ext1 m; rw [transactions,follow_at,follow_at,transactions]; apply congr_arg F; ext1 k; obtain ⟨v|v,rfl⟩:= (parts h).surjective k
    · have ht : InjOn (germL h) Set.univ:= (show Injective (fun i:P=> germL h i) from fun i j h'=> Subtype.ext (congr_arg (fun x : merge h=> x.val) h')).injOn
      change Function.update (joinP h m A) _ _ (germL h v)=joinP h _ A (germL h v); by_cases he:v=i; subst v; simp [joinP,heli_left]; simp [joinP, heli_left, update_of_ne he, update_of_ne (show germL h v≠germL h i from fun hh=> he (ht (Set.mem_univ v) (Set.mem_univ i) hh))]
    change Function.update (joinP h m A) _ _ (germR h v)=joinP h _ A (germR h v); rw [update_of_ne (show germR h v≠ germL h i from (parts h).injective.ne (show Sum.inr v ≠ Sum.inl i from Sum.inr_ne_inl))]; simp [joinP,heli_right]
end
section
variable (hR: R ≤ P)(hU:U≤ Q)(K:Free R U)(v:Program S (merge K))
lemma converse_left : (garland (merge_le h hR hU (he:=K)) v) ∘ germL h= garland hR (v ∘ germL K):=by
    ext1 i; let y(x):= v (germL K x); let hz:= merge_le h (he:=K) hR hU; let f:=germL K; have he:Injective f:= fun m n h=>Subtype.ext (congr_arg (fun x: merge K=> x.val) h)
    let s:=dialogues hR i; let t:=dialogues hz (germL h i); have hu:t=s.image f:=by
       ext1 q; obtain ⟨j|j,rfl⟩:= (parts K).surjective q
       · change f j∈ t↔ f j∈ _; have hh : f j∈s.image f ↔ j∈s:= ⟨fun hv=> by (obtain ⟨z,h,hv⟩:= Finset.mem_image.mp hv; exact he hv ▸ h),fun hh=> Finset.mem_image_of_mem f hh⟩; rw [hh]; unfold t s; exact (members' _ _ _).trans (members' hR j i).symm
       change germR K j ∈ t ↔ germR K j ∈ s.image f; unfold t
       have h1:germR K j∉ s.image f:= fun hh=> by obtain ⟨u,_,hp⟩:=mem_image.mp hh; exact (parts K).injective.ne (show Sum.inl u ≠ Sum.inr j from Sum.inl_ne_inr) hp
       have h2: assign hz (germR K j) = germR h (assign hU j):= right_travel h hR hU j
       rw [members,h2]; exact iff_of_false ((parts h).injective.ne (show Sum.inr (assign hU j) ≠ Sum.inl i from Sum.inr_ne_inl)) h1
    change (∏ i∈t,v i)=∏ j∈s,y j; rw [hu,prod_image (g:=f) (f:=v) he.injOn]
lemma converse_right : (garland (merge_le h hR hU (he:=K)) v) ∘ germR h= garland hU (v ∘ germR K):=by
    ext1 i; let y(x):= v (germR K x); let hz:= merge_le h (he:=K) hR hU; let f:=germR K; have he:Injective f:= fun m n h=>Subtype.ext (congr_arg (fun x: merge K=> x.val) h)
    let s:=dialogues hU i; let t:=dialogues hz (germR h i); have hu:t=s.image f:=by
       ext1 q; obtain ⟨j|j,rfl⟩:= (parts K).surjective q; swap
       · change f j∈ t↔ f j∈ _; have hh : f j∈s.image f ↔ j∈s:= ⟨fun hv=> by (obtain ⟨z,h,hv⟩:= Finset.mem_image.mp hv; exact he hv ▸ h),fun hh=> Finset.mem_image_of_mem f hh⟩; rw [hh]; unfold t s; exact (members' _ _ _).trans (members' hU j i).symm
       change germL K j ∈ t ↔ germL K j ∈ s.image f; unfold t
       have h1:germL K j∉ s.image f:= fun hh=> by obtain ⟨u,_,hp⟩:=mem_image.mp hh; exact (parts K).injective.ne (show Sum.inr u ≠ Sum.inl j from Sum.inr_ne_inl) hp
       have h2: assign hz (germL K j) = germL h (assign hR j):= left_travel h hR hU j
       rw [members,h2]; exact iff_of_false ((parts h).injective.ne (show Sum.inl (assign hR j) ≠ Sum.inr i from Sum.inl_ne_inr)) h1
    change (∏ i∈t,v i)=∏ j∈s,y j; rw [hu,prod_image (g:=f) (f:=v) he.injOn]
end
end YM.Frontier6.Bouquet
