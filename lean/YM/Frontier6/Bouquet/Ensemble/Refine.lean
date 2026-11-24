import YM.Frontier6.Bouquet.Ensemble.Blocks

/-! Refinement of a frontier is within THE SAME underlying set of slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Ensemble
open Function Set Finset
open scoped Topology BigOperators Classical
variable {P Q R: Ensemble}
def divides (P Q:Ensemble): Prop:= P.Along=Q.Along ∧ ∀ p∈ P.choose, ∃ q∈Q.choose,p ≤ q
instance : LE Ensemble := ⟨divides⟩
lemma ref_self (P:Ensemble) : P ≤ P:= ⟨rfl,fun p hp=>⟨p,hp,le_rfl⟩⟩
lemma ref_pass (h:P ≤ Q)(he:Q ≤ R): P ≤ R:=by
   constructor; exact Eq.trans h.1 he.1; intro p hp; obtain ⟨q,hq,hpq⟩:=h.2 p hp; obtain ⟨r,hr,hqr⟩:=he.2 q hq; exact ⟨r,hr,le_trans hpq hqr⟩
lemma not_cross (h:P ≤ Q){p q: Pod}(hp:p∈ P.choose) (hq:q∈ Q.choose){i:Slot}(he:i∈ p.val)(hh:i∈ q.val):p ≤ q:=by
    obtain ⟨r,hr,h⟩:= h.2 p hp; rwa [← (same hq hr hh (h he))] at h
instance : PartialOrder Ensemble where
    le_refl:= ref_self
    le_trans _ _ _:= ref_pass
    le_antisymm P Q h h':=by
       have hh (P Q:Ensemble)(h:P ≤ Q)(h':Q ≤ P): P.choose⊆Q.choose:=by
           intro p hp; obtain ⟨q,hq,hh⟩:=h.2 p hp; exact (le_antisymm hh (not_cross h' hq hp (hh p.here_mem) p.here_mem)) ▸ hq
       exact ext (Subset.antisymm (hh _ _ h h') (hh _ _ h' h)) -- ident

section
variable (H:P≤Q)
include H
lemma ref_slots : P.Along=Q.Along:= H.1
-- index map and its surjectivity. CoeSort Ensemble to Subtype enables dot notation?
def assign (p:P) : Q:= ⟨(H.2 p p.property).choose, (H.2 p p.property).choose_spec.1⟩
lemma inside (p:P): p.val ≤ (assign H p).val:= (H.2 p.val p.property |>.choose_spec.2) -- defin?
lemma assigned (p:P)(q:Q)(he:p.val ≤ q.val): assign H p=q:= serial Q ((inside H p) p.val.here_mem) (he p.val.here_mem)
lemma assign_surjects : Surjective (assign H):=by
   intro q; let i:= q.val.here; obtain ⟨p,hp,h⟩:= (mem_along P i).mp ((ref_slots H) ▸ (mem_along Q i).mpr ⟨_,q.property,q.val.here_mem⟩)
   exact ⟨⟨p,hp⟩, assigned H _ q (not_cross H hp q.property h q.val.here_mem)⟩
lemma via (K:Q≤R)(p:P): assign (H.trans K) p= assign K (assign H p):= assigned _ _ _ (le_trans (inside H p) (inside K _)) -- syntax
lemma rank_le : Q.choose.card ≤ P.choose.card:=by simpa only [Fintype.card_coe] using (show Fintype.card Q.choose ≤ Fintype.card P.choose from Fintype.card_le_of_surjective _ (assign_surjects H))
lemma injective_assign (h:Injective (assign H)): P=Q:=by
   apply le_antisymm H; constructor; exact H.1.symm; intro q hq; obtain ⟨p,hp⟩:= assign_surjects H ⟨q,hq⟩; refine ⟨_,p.property,?_⟩; intro i hi
   obtain ⟨s,hs,hk⟩:= (mem_along P i).mp ((ref_slots H) ▸ (mem_along Q i).mpr ⟨_,hq,hi⟩)
   exact h (show assign H ⟨s,hs⟩=assign H p from (assigned H ⟨s,hs⟩ ⟨q,hq⟩ (not_cross H hs hq hk hi)).trans hp.symm) ▸ hk -- match
end
lemma rank (H:P<Q): Q.choose.card < P.choose.card:=lt_of_le_of_ne (rank_le H.le) (fun h=> H.ne (injective_assign H.le (Fintype.bijective_iff_surjective_and_card (assign H.le) |>.mpr ⟨assign_surjects _,(by simpa only [Fintype.card_coe] using! h.symm)⟩ |>.1)))
-- refinements form a finite set.
abbrev stages (S:Finset Slot) : Set Pod:= {p|p.val⊆ S}
lemma stages_finite (s:Finset Slot) : (stages s).Finite:=by
   apply ((finite_toSet s.powerset).preimage (f:=fun x:Pod=> x.val) Subtype.coe_injective.injOn).subset; intro p hp; exact mem_powerset.mpr hp
abbrev Down (P:Ensemble) := {Q:Ensemble // Q ≤ P}
lemma down_finite (P:Ensemble) : {Q: Ensemble|Q≤P}.Finite:=by
   let F:= (stages_finite P.Along).toFinset
   refine ((finite_toSet (F.powerset)).preimage (f:=fun Q:Ensemble=>Q.choose) (fun p _ q _ he=> ext he)).subset ?_; intro p he
   apply Finset.mem_powerset.mpr; intro s hs; apply (stages_finite P.Along).mem_toFinset.mpr; intro i hi; exact (ref_slots (show p≤ P from he)) ▸ ((mem_along p i).mpr ⟨_,hs,hi⟩)
instance (P:Ensemble) : Fintype (Down P):= (down_finite P).fintype
instance (P:Ensemble) : Nonempty (Down P):=⟨⟨_,le_refl P⟩⟩
end YM.Frontier6.Bouquet.Ensemble
