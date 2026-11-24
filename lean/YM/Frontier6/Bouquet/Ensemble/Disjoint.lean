import YM.Frontier6.Bouquet.Ensemble.Refine

/-! Disjoint offsets and grouping partitions -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Ensemble
open Function Set Finset
open scoped Topology BigOperators Classical
variable (P Q R: Ensemble){p:Pod}
def Free : Prop:= Disjoint P.Along Q.Along
lemma listed (p:Pod) (he:p∈ P.choose): p.val⊆ P.Along:= fun i hi=> (mem_along P i).mpr ⟨p,he,hi⟩
variable {P Q}
namespace Free
variable (h: Free P Q)
include h
lemma separate (p q:Pod)(hp:p∈P.choose)(hq:q∈Q.choose): Disjoint p.val q.val:= Disjoint.mono (listed _ _ hp) (listed _ _ hq) h -- fill
lemma choose : Disjoint P.choose Q.choose:=Finset.disjoint_left.mpr fun i j h' => i.not_disjoint (h.separate i i j h')
lemma symm : Free Q P := Disjoint.symm h
lemma refines {A B : Ensemble}(he:A ≤ P)(hl:B≤Q): Free A B:= by unfold Free; rw [ref_slots he,ref_slots hl]; exact h
end Free

def merge (h:Free P Q) : Ensemble := ⟨P.choose∪Q.choose, (by
    intro i hi j hj he; rcases Finset.mem_union.mp hi with hi|hi <;> rcases Finset.mem_union.mp hj with hj|hj
    exacts [P.pairwise hi hj he,h.separate _ _ hi hj,h.symm.separate _ _ hi hj,Q.pairwise hi hj he]) ⟩
section
variable (h:Free P Q)
lemma along_merge : Along (merge h)=P.Along∪Q.Along:= by unfold Along merge; rw [Finset.union_biUnion]
def germL (p:P) : merge h:= ⟨p.val, mem_union_left _ p.property⟩
def germR (p:Q) : merge h:= ⟨p.val, mem_union_right _ p.property⟩
def parts : P ⊕ Q ≃ merge h:=Equiv.ofBijective (Sum.elim (germL h) (germR h)) (by
   constructor
   · rintro (i|i) (j|j) he
     exacts [congr_arg _ (Subtype.ext (congr_arg (fun x:merge h=> x.val) he)), (Finset.disjoint_left.mp h.choose i.property ((show i.val=j.val from congr_arg (fun x:merge h=> x.val) he) ▸ j.property)).elim, (Finset.disjoint_left.mp h.choose j.property ((show j.val=i.val from congr_arg (fun x:merge h=> x.val) he.symm) ▸ i.property)).elim, congr_arg _ (Subtype.ext (congr_arg (fun x:merge h=> x.val) he))]
   rintro ⟨x,hx⟩; rcases mem_union.mp hx with h|h; exacts [⟨Sum.inl ⟨x,h⟩,rfl⟩,⟨Sum.inr ⟨x,h⟩,rfl⟩])
section
variable {A B:Ensemble}
lemma merge_le {he:Free A B}(hA:A ≤ P)(hB:B ≤ Q): merge he ≤ merge h:= by
   constructor; rw [along_merge,along_merge,ref_slots hA,ref_slots hB]; intro a ha; rcases Finset.mem_union.mp ha with hl|hr
   · obtain ⟨x,hx,H⟩:= hA.2 a hl; exact ⟨x, mem_union_left _ hx,H⟩
   obtain ⟨x,hx,H⟩:= hB.2 a hr; exact ⟨x,mem_union_right _ hx,H⟩
lemma left_travel {he:Free A B}(hx:A≤P)(hv:B≤Q)(a:A):assign (merge_le h (he:=he) hx hv) (germL he a)=germL h (assign hx a):= assigned _ _ _ (inside hx a)
lemma right_travel {he:Free A B}(hx:A≤P)(hv:B≤Q)(a:B):assign (merge_le h (he:=he) hx hv) (germR he a)=germR h (assign hv a):= assigned _ _ _ (inside hv a)
end
lemma rank_merge : (merge h).choose.card=P.choose.card+Q.choose.card:= Finset.card_union_of_disjoint h.choose
end
-- exclude pieces of a chart
variable (P)
def except (p:Pod) : Ensemble:= ⟨P.choose.erase p, fun i hi j hj he=> P.pairwise (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hj) he⟩
lemma except_le (p:Pod): Along (except P p) ⊆ P.Along := by rintro i hi; obtain ⟨q,hq,h⟩:=(mem_along _ _).mp hi; exact (mem_along ..).mpr ⟨_,mem_of_mem_erase hq,h⟩
lemma except_free {p:Pod}(he:p∈P.choose):Free (only p) (except P p):=by
   unfold Free; rw [along_only]; refine Finset.disjoint_left.mpr (fun i hi he'=>?_); obtain ⟨q,hq,h⟩:=(mem_along _ _).mp he'; exact ne_of_mem_erase hq (same (Finset.mem_of_mem_erase hq) he h hi)
lemma except_eq {p:Pod} (h:p∈ P.choose): P=merge (except_free P h):=by
   refine ext ?_; change P.choose = {p} ∪ P.choose.erase p; rw [Finset.singleton_union,insert_erase h]
end YM.Frontier6.Bouquet.Ensemble
