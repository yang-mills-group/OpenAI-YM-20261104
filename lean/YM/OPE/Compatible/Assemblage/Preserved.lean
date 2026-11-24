import YM.OPE.Grouping.Replicate
/-!
# Simultaneous remounting preserves all untouched individual carriers

One step needed also for sweeps without uniform tree ratios. The
*actual* flagged expression, not just its price. Only single untouched
fibers are claimed: for any fiber of Salt `Solo` type, take care to carry
its global spice separately. Then the operation honors every singleton
forced expression of exactly that slot. Unmarked fee result S.taxed is
orthogonal. This allows using independent movements of untouched
singletons across events without changing their labels/RG continuation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J A : Type*} [DecidableEq V] [DecidableEq I][DecidableEq J] [DecidableEq A][Fintype V] [Fintype A] {n:Side}{G:Gauge}
variable (L:Fibers A V)

def SingleFiber (v:V) := L.contents v={L.twig v}
lemma sola (v:V) (hv:L.SingleFiber v)(b:A) : L.bunch b=v ↔ b=L.twig v:= by rw [← L.focuses,hv]; simp
lemma embraces (b:V) : L.span ((Bud A).fire (L.twig b))=(Bud V).fire b:=by
    apply Subtype.ext; change Finset.image _ {L.twig b}={b}; rw [image_singleton,L.sectioned]
lemma solo_plena (v:V)(hv:L.SingleFiber v): L.plena ((Bud V).fire v)=(Bud A).fire (L.twig v):=by
    apply Subtype.ext; change Finset.biUnion {v} _=_; rw [singleton_biUnion]; exact hv
namespace Deck
variable {L}
variable (D:Deck V A L I J G n) (t:ℝ)(U:Config G n)(h:D.Wet t)(v:V)(hv:L.SingleFiber v)
    (h_c : ∀ i:J,(D.mode_ (.inr i)=(Bud A).fire (L.twig v))→ D.cover (.inr i)=(D.spill i).1)
    (h_a : ∀ i:I,(D.mode_ (.inl i)=(Bud A).fire (L.twig v))→ D.ash i → D.toll (.inl i) U=0)
include hv h
set_option linter.unusedSectionVars true in
lemma solitary (p:D.Ink)(he:D.quip (.inr p)=(Bud V).fire v) : D.plank (.inr p)=(Bud A).fire (L.twig v):=by
    refine (fun (_ : D.Wet t)=> ?_) h
    have ht:= (D.run (.inr p)).ready; change D.plank (.inr p)= L.plena (D.quip (.inr p)) at ht; rw [he] at ht; exact ht.trans (L.solo_plena v hv)
lemma led (p:D.Ink)(he:D.quip (.inr p)=(Bud V).fire v){i:I⊕J}(hi:i∈p.val)(hg:(D.mode_ i).val.Nonempty) : D.mode_ i=(Bud A).fire (L.twig v):=by
    apply Subtype.ext; change _={_}
    have ht : p.val.biUnion (fun i=>(D.mode_ i).val)={L.twig v}:=congr_arg (fun i:(Bud A).Mode=>i.val) (D.solitary t h v hv p he)
    have hh (a)(ha:a∈(D.mode_ i).val): a=L.twig v:=mem_singleton.mp (ht ▸ mem_biUnion.mpr ⟨_,hi,ha⟩)
    obtain ⟨a,ha⟩:=hg; exact eq_singleton_iff_unique_mem.mpr ⟨hh a ha ▸ ha,hh⟩
lemma link_tag (p:D.Ink)(he:D.quip (.inr p)=(Bud V).fire v){a b:I⊕J}(hw: Collide.link D.kiln.mention p.val a b) : a=b:=by
    induction hw with
    | refl=>rfl
    | @tail x y path hm ih=>
      apply ih.trans; obtain ⟨hx,hy,u,h1,h2⟩:=hm
      obtain ⟨i,-,hi⟩:=(L.spans (D.mode_ x) u).1 h1; obtain ⟨j,-,hj⟩:=(L.spans (D.mode_ y) u).1 h2
      by_contra hh; exact disjoint_left.mp (p.property.buys.1 hx hy hh) hi (by change i ∈ (D.mode_ y).val; rw [(D.led t h v hv p he hy ⟨_,hj⟩).trans (D.led t h v hv p he hx ⟨_,hi⟩).symm]; exact hi)

include h_c h_a
lemma cargo (p:D.Ink)(he:D.quip (.inr p)=(Bud V).fire v)(hp : D.nectar t U p≠0):
    ∃ i:J,D.mode_ (.inr i)=(Bud A).fire (L.twig v) ∧ p.val={Sum.inr i}:=by
    unfold nectar at hp; split at hp
    swap; · contradiction
    have hw(i:I⊕J) (hi: i∈p.val): D.toll i U ≠ 0:=fun hx=> hp (prod_eq_zero (show i∈D.glyph (.inr p) from hi) hx)
    have hk(i:I): Sum.inl i∉p.val:= by
       intro hi; obtain ⟨j,-,hD,hx⟩:= D.kiln.takes_mole p.property.fire hi |>.mp (D.blot _ p.property.wet)
       rw [← D.link_tag t h v hv p he hx] at hD
       exact hw _ hi (h_a i (D.led t h v hv p he hi (h.clean i)) hD)
    have hh (i:J)(hi:Sum.inr i∈p.val): D.cover (.inr i)=(D.spill i).1:=by
       by_cases h':(D.mode_ (.inr i)).val.Nonempty
       · exact h_c i (D.led t h v hv p he hi h')
       apply h.plain; simp [roster,Fibers.span,not_nonempty_iff_eq_empty.mp h']
    have ha: p.val.biUnion (fun i=>(D.mode_ i).val)={L.twig v}:=congr_arg (fun i:(Bud A).Mode=>i.val) (D.solitary t h v hv p he)
    obtain ⟨i|i,hi,ht⟩:= mem_biUnion.mp (ha.symm ▸ mem_singleton_self (L.twig v)); exact (hk i hi).elim
    refine ⟨i,D.led t h v hv p he hi ⟨_,ht⟩,eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj=>?_⟩⟩
    induction p.property.fire.2 _ hi j hj with
    | refl => rfl
    | @tail k j path hb ih =>
      rw [ih hb.1] at hb; obtain ⟨_,h₂,c,h₃,h₄⟩:=hb
      cases c with
      | inl a=> exact (D.link_tag t h v hv p he (.single ⟨hi,h₂, a, D.kiln.fuel_left.mp h₃,D.kiln.fuel_left.mp h₄⟩)).symm
      | inr b=>
        cases j with
        | inl c=> exact (hk c h₂).elim
        | inr c=>
          by_contra he; have ht:b∈(D.spill i).1:= hh i hi ▸ ((D.kiln.fuel_right).1 h₃).2; have hx:b∈(D.spill c).1:=hh c h₂ ▸ ((D.kiln.fuel_right).1 h₄).2
          exact disjoint_left.mp (p.property.old (mem_toRight.mpr h₂) (mem_toRight.mpr hi) fun e=>he (congr_arg _ e)) hx ht

omit h_c h_a
set_option linter.unusedSectionVars true in
lemma admits_single (i:J)(hi:D.mode_ (.inr i)=(Bud A).fire (L.twig v)) : D.Tank {Sum.inr i}:=by
    refine (fun (_ : DecidableEq I) (_ : DecidableEq J) (_ : D.Wet t)=> ?_) (inferInstance : DecidableEq I) (inferInstance : DecidableEq J) h
    refine { old:= (?_), buys:= fits_singleton _ _, ready:= ?_, fire:= ⟨singleton_nonempty _,fun a ha b hb=> by rw [mem_singleton.mp ha,mem_singleton.mp hb]; exact .refl⟩, wet:=⟨i,mem_toRight.mpr (mem_singleton_self _)⟩ }
    · have hp : toRight ({Sum.inr i}:Finset (I⊕J))={i}:=by ext; simp
      simp [hp]
    have hp: L.Pays ((Bud A).fire (L.twig v)):=by unfold Pays; rw [L.embraces,L.solo_plena _ hv]
    convert hp using 1; apply Subtype.ext; change Finset.biUnion {Sum.inr i} _= _; rw [singleton_biUnion]; exact congr_arg Subtype.val hi
include h_c
set_option linter.unusedSectionVars true in
lemma issued (p:D.Ink)(i:J)(hi:D.mode_ (.inr i)=(Bud A).fire (L.twig v))(ht:p.val={Sum.inr i}) :
    D.fuse p.val=D.spill i ∧ D.quip (.inr p)=(Bud V).fire v∧ D.nectar t U p=D.toll (.inr i) U:=by
    refine (fun (_ : L.SingleFiber v)=> ?_) hv
    have he: D.reach p.val=(D.spill i).1:=by simp [reach,ht,h_c _ hi]
    have ha:D.stain p.val=(D.spill i).2:=by unfold stain; rw [show p.val.toRight={i} from by rw [ht];ext; simp];simp
    refine ⟨by simp [fuse,he,ha],?_,?_⟩
    · apply Subtype.ext; rw [paint,show D.glyph (.inr p)={Sum.inr i} from ht,singleton_biUnion]; change (L.span (D.mode_ _)).val=_; rw [hi,L.embraces]
    unfold nectar; rw [he,ha]; split
    · unfold bud; rw [show D.glyph (.inr p)={Sum.inr i} from ht]; simp
    next ht'=> exact (Classical.byContradiction (fun hn=> ht' (h.allows i U hn))).symm
variable [Fintype I][Fintype J]
include h_a
lemma carat (z:Box n) : (D.clay t z U).part ((Bud V).fire v)= (cram D.spill (fun i=>Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)) z).part ((Bud A).fire (L.twig v)):=by
   let q:={i:J//D.mode_ (.inr i)=(Bud A).fire (L.twig v)}
   let a:=fun i:D.Ink=> if D.fuse i.val=z then (Poly.send (D.quip (.inr i)) (D.nectar t U i)).part ((Bud V).fire v) else 0
   let b:=fun i:J=>if D.spill i=z then (Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)).part ((Bud A).fire (L.twig v)) else 0
   let f (i:q):D.Ink:=⟨{Sum.inr i.val},D.admits_single t h v hv i.val i.property⟩
   have hf: Injective f:= fun i j he=> Subtype.ext (Sum.inr.inj (Finset.singleton_inj.mp (congr_arg Subtype.val he)))
   have hu(i:q): a (f i)=b i.val:=by
      have hx:=D.issued t U h v hv h_c (f i) i.val i.property rfl; unfold a b;rw [hx.1,hx.2.1,hx.2.2,i.property];simp [Poly.part_send]
   change (cram (fun i:D.Ink=>D.fuse i.val) (fun i=>Poly.send (D.quip (.inr i)) (D.nectar t U i)) z).part _= _
   unfold cram; rw [Poly.share (hs:=Summable.of_finite),Poly.share (hs:=Summable.of_finite)];
   erw [_root_.tsum_subtype {i:D.Ink|D.fuse i.val=z} (fun i=> (Poly.send (D.quip (.inr i)) (D.nectar t U i)).part ((Bud V).fire v)),_root_.tsum_subtype {i:J|D.spill i=z} (fun i=>(Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)).part ((Bud A).fire (L.twig v)))]
   suffices hp:(∑' i,a i)=∑' i,b i by simpa [a,b,Set.indicator] using hp
   rw [← hf.tsum_eq (fun i hi=>?_)]
   · simp_rw [hu]; refine tsum_subtype_eq_of_support_subset (fun i (hi: b i≠0)=>?_)
     unfold b at hi; split at hi; swap; · contradiction
     rw [Poly.part_send] at hi; split at hi; next he=> exact he.symm
     contradiction
   change a i≠0 at hi; unfold a at hi; split at hi; swap; · contradiction
   rw [Poly.part_send] at hi; split at hi
   next he=> obtain ⟨i',hV,hZ⟩:= D.cargo t U h v hv h_c h_a _ he.symm hi; exact ⟨⟨i',hV⟩,Subtype.ext hZ.symm⟩
   contradiction
end Deck
namespace Salt
variable {L}
lemma kept_fire (Z:Salt V A L G n)(t:ℝ)(U:Config G n)(h:Z.Breeze t)(v:V)(hv:L.SingleFiber v)(hz:Z.pepper (L.twig v)=0)(z:Box n):
   (Z.soil t z U).part ((Bud V).fire v)=(Z.river z U).part ((Bud A).fire (L.twig v)):=by
    refine ((Z.vessel t).carat t U (Z.wet t h) v hv ?_ ?_ z).trans ?_
    · intro i ht; change i.val.2 = _ at ht; change Z.kiln i.val.1.1 _= _; unfold kiln; rw [ht,L.embraces]; change i.val.1.1∪Finset.image Z.focus {v}=i.val.1.1
      rw [image_singleton]; apply union_eq_left.mpr; rw [singleton_subset_iff]; exact i.property.2 (mem_image_of_mem Z.grain (ht.symm ▸ mem_singleton_self _))
    · rintro ⟨i|i,s⟩ ht he
      · have hx:= (Bud A).fire_inj _ _ |>.mp ht; change Z.bud t U (Sum.inl i,s) = 0
        unfold bud; split; next=>exact hx.symm ▸ hz
        rfl
      change i.val.2=_ at ht; change s=false at he; change Z.bud ..=0
      unfold bud; split
      next hb=>
        change (Z.air i.val.1 U).part i.val.2=0; by_contra hh
        have hg:Healthy t i.val.1 U:= (h.home _).permits U (fun he=>hh (by rw [he,Poly.part_nil]))
        have hp : Z.kiln (Z.leaf (Sum.inr i)) (Z.marker (.inr i))=i.val.1:=by change i.val.1∪ (L.span i.val.2).val.image Z.focus=i.val.1; rw [ht,L.embraces]; change i.val.1∪Finset.image Z.focus {v}= i.val.1; rw [image_singleton]; apply union_eq_left.mpr; rw [singleton_subset_iff]; exact i.property.2 (mem_image_of_mem _ (ht.symm ▸ mem_singleton_self _))
        exact Bool.false_ne_true (he.symm.trans (hb.mp (hp.symm ▸ hg)))
      rfl
    exact congr_arg (fun p:Poly (Bud A)=>p.part ((Bud A).fire (L.twig v))) (Z.fieldSpend t U h z)
end Salt
end YM.MergeProof.Ribbons.Fibers
