import YM.OPE.Grouping.River
import YM.OPE.Grouping.Birth
/-!
# When a salt fiber has one old mark ...
It turns out one can retrieve the old forced profile exactly, provided just
that the global unit is omitted from splitting in its direct basic terms! This
gives a way around carrying unbounded cutoff growth on branches **already at**
their supported k-height (or not yet there).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}
variable {Y : Type*} [Fintype Y][DecidableEq Y] {L : Fibers Y V}
-- keep unambig type signature
/-- Ties explicitly use chosen representative. -/
def Solo (L:Fibers Y V)(v:V):=∀ i,L.bunch i=v→L.twig v=i
namespace Solo
variable {v:V}(h:L.Solo v)
include h
lemma content : L.contents v={L.twig v}:= by
    ext i; rw [focuses,mem_singleton]; exact ⟨fun hv=>(h i hv).symm,fun hp=> hp ▸ L.sectioned v⟩
lemma fire : L.plena ((Bud V).fire v)=(Bud Y).fire (L.twig v) := Subtype.ext (by change Finset.biUnion {v} _=_; rw [singleton_biUnion]; exact content h)
end Solo
namespace Deck
variable [DecidableEq I][DecidableEq J](D:Deck V Y L I J G n) (t:ℝ)(U:Config G n)(h:D.Wet t)
variable {v:V} (hv:L.Solo v)
open MeasureTheory Set Ac Push.Local Push.GridApprox.Nil
open Collide
/-- Assume only the vessel properties at single old mark terms after peg rounding. Only invoked after psi hook kept exactly. -/
structure QuietAt (D:Deck V Y L I J G n) (v:V) (U:Config G n):Prop where
    cover i:(D.mode_ (Sum.inr i)).val ⊆ {L.twig v}→D.cover (.inr i)=(D.spill i).1
    clean i:(D.mode_ (Sum.inl i)).val⊆{L.twig v}→ D.toll (Sum.inl i) U ≠ 0→ ¬ D.ash i
include hv
lemma roster_same (p:D.Ink)(hp:D.quip (.inr p)=(Bud V).fire v) : ∀ j∈p.val,(D.mode_ j).val⊆{L.twig v}:=by
    have hx:D.plank (.inr p)=(Bud Y).fire (L.twig v):=by rw [← hv.fire,← hp]; exact (D.run (.inr p)).ready
    intro j hj; have hh : (D.glyph (.inr p)).biUnion (fun i=>(D.mode_ i).val)={L.twig v}:=congr_arg Subtype.val hx; rw [← hh]; exact subset_biUnion_of_mem (fun i=> (D.mode_ i).val) (show j∈D.glyph (.inr p) from hj)
include h
lemma lone {p:D.Ink}(hr:D.QuietAt v U) (hp:D.quip (.inr p)=(Bud V).fire v) (hU:D.nectar t U p ≠ 0) : ∃ i:J,D.mode_ (.inr i)=(Bud Y).fire (L.twig v)∧p.val={Sum.inr i}:=by
    let D':=D.kiln; let s:=p.val; have hs:=D.roster_same hv p hp
    have hk:D.kiln.Takes s:= D.blot _ p.property.wet
    have hm(i)(hi:i∈ p.val): D.toll i U≠0:=by unfold nectar at hU; split at hU; exact fun he=> hU (prod_eq_zero hi he); contradiction
    have he (i)(hb:i∈p.val)(j)(hj:j∈p.val) (hk:Collide.meets D.kiln.mention i j): i=j:=by
        by_contra hn; obtain ⟨v',ha,he⟩:=hk; obtain ⟨b,hv,-⟩:= mem_image.mp ha; obtain ⟨c,hx,-⟩:=mem_image.mp he
        exact Finset.disjoint_left.mp (p.property.buys.1 hb hj hn) hv (((mem_singleton.mp (hs i hb hv)).trans (mem_singleton.mp (hs j hj hx)).symm) ▸ hx) -- b'
    have hy(i:I): Sum.inl i∉p.val:=by
        intro hi; have hV:D.kiln.Hot s (Sum.inl i):= (D.kiln.takes_mole p.property.fire hi).1 hk; obtain ⟨j,hj,ht,hF⟩:=hV
        have hg:j=Sum.inl i:=by clear ht hj; induction hF with
                                     | refl=>rfl
                                     | tail _ ht ih=> exact (he _ ht.1 _ ht.2.1 ht.2.2).symm.trans ih
        exact hr.clean i (hs _ hi) (hm _ hi) (show D.kiln.dirty (.inl i) from hg ▸ ht)
    obtain ⟨i,hi⟩:=p.property.wet; have hx:Sum.inr i∈p.val:= mem_toRight.mp hi
    have hz(j:J)(hj:Sum.inr j∈p.val): D.cover (Sum.inr j)=(D.spill j).1:=hr.cover _ (hs _ hj)
    have hf(j)(hj:j∈p.val): j=Sum.inr i:=by
       induction p.property.fire.2 _ hx j hj with
       | refl=>rfl
       | @tail k j _ hb ih=>
         have hk:=ih hb.1; obtain ⟨h1,h2,x,h3,h4⟩:=hb; cases x with
         | inl z=> exact (he _ h1 _ h2 ⟨z,D.kiln.fuel_left.mp h3,D.kiln.fuel_left.mp h4⟩).symm.trans hk
         | inr z=>
           subst k; cases j with
           | inl j=>exact False.elim (hy j hj)
           | inr j=> by_contra hn; have ha : z∈D.cover (Sum.inr i):= (D.kiln.fuel_right.mp h3).2; have he:z∈ D.cover (Sum.inr j):=(D.kiln.fuel_right.mp h4).2; exact Finset.disjoint_left.mp (p.property.old hi (mem_toRight.mpr hj) fun e=>hn (e ▸ rfl)) (show z∈(D.spill i).1 from hz i hx ▸ ha) (show z∈(D.spill j).1 from hz j hj ▸ he)
    refine ⟨i,?_ ,eq_singleton_iff_unique_mem.mpr ⟨hx,hf⟩⟩
    have hZ : p.val={Sum.inr i}:= eq_singleton_iff_unique_mem.mpr ⟨hx,hf⟩
    have hV : (D.plank (.inr p)).val=(D.mode_ (.inr i)).val:=by change p.val.biUnion _=_; rw [hZ,singleton_biUnion]
    rw [← hv.fire,← hp]; exact (Subtype.ext hV.symm).trans (D.run (.inr p)).ready
lemma acceptsSolo (i:J)(hs:D.mode_ (.inr i)=(Bud Y).fire (L.twig v)): D.Tank {Sum.inr i}:=by
    refine { old:= (?_), buys:= fits_singleton _ _, ready:=?_, fire:=⟨singleton_nonempty _,fun a ha b hb=> by rw [mem_singleton.mp ha,mem_singleton.mp hb]; exact .refl⟩, wet:=⟨i,mem_toRight.mpr (mem_singleton_self _)⟩ }
    · have hp : toRight ({Sum.inr i}:Finset (I⊕J))={i}:=by ext; simp
      simp [hp]
    have hh : unionTag D.mode_ {Sum.inr i} (fits_singleton ..)=D.mode_ (.inr i):=Subtype.ext (by change Finset.biUnion ({Sum.inr i} : Finset (I⊕J)) _=_; rw [singleton_biUnion])
    rw [hh,hs,← hv.fire]; unfold Pays; rw [reband]
lemma sentSolo {p:D.Ink}{i:J}(hr:D.QuietAt v U)(hp:p.val={Sum.inr i})(hs:D.mode_ (.inr i)=(Bud Y).fire (L.twig v)): D.fuse p.val=D.spill i ∧ D.quip (.inr p)=(Bud V).fire v ∧ D.nectar t U p=D.toll (.inr i) U:=by
    have he:D.reach p.val=(D.spill i).1:=by simp only [reach,hp,singleton_biUnion]; exact hr.cover _ (hs ▸ Finset.Subset.refl _)
    have ha:D.stain p.val=(D.spill i).2:=by
       unfold stain; rw [show p.val.toRight={i} from (by rw [hp];ext; simp)]; simp
    have hq:D.plank (.inr p)=D.mode_ (.inr i):=Subtype.ext (by change p.val.biUnion _=_; rw [hp,singleton_biUnion])
    refine ⟨by simp [fuse,he,ha],by rw [quip,hq,hs,← hv.fire,L.reband],?_⟩
    unfold nectar; rw [he,ha]; split
    · unfold bud; rw [(show D.glyph (.inr p)={Sum.inr i} from hp)]; simp
    next hh=> exact (Classical.byContradiction (fun hu=> hh (h.allows i U hu))).symm
variable [Fintype I][Fintype J]
lemma soberSolo (ht:D.QuietAt v U) (z:Box n):
    (cram (fun i:D.Ink=>D.fuse i.val) (fun i=>Poly.send (D.quip (.inr i)) (D.nectar t U i)) z).part ((Bud V).fire v)=
      (cram D.spill (fun i=>Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)) z).part ((Bud Y).fire (L.twig v)):=by
   let a:=fun i:D.Ink=> if D.fuse i.val=z then (Poly.send (D.quip (.inr i)) (D.nectar t U i)).part ((Bud V).fire v) else 0
   let b:=fun i:J=>if D.spill i=z then (Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)).part ((Bud Y).fire (L.twig v)) else 0
   let u:={i:J| D.mode_ (.inr i)=(Bud Y).fire (L.twig v)}; let f (i:u) : D.Ink:=⟨{Sum.inr i.val},D.acceptsSolo t h hv _ i.property⟩
   have hf: Injective f:= fun i j he=> Subtype.ext (Sum.inr.inj (Finset.singleton_inj.mp (congr_arg Subtype.val he)))
   have he(i:u): a (f i)=b i.val:=by
      have hx:=D.sentSolo t U h hv (p:=f i) ht rfl i.property; unfold a b; rw [hx.1,hx.2.1,hx.2.2,(show D.mode_ (.inr i.val)= _ from i.property)]; simp [Poly.part_send]
   unfold cram; rw [Poly.share (hs:=Summable.of_finite),Poly.share (hs:=Summable.of_finite)];
   erw [_root_.tsum_subtype {i:D.Ink|D.fuse i.val=z} (fun i=> (Poly.send (D.quip (.inr i)) (D.nectar t U i)).part ((Bud V).fire v)),_root_.tsum_subtype {i:J|D.spill i=z} (fun i=>(Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)).part ((Bud Y).fire (L.twig v)))]
   suffices hp:(∑' i,a i)=∑' i,b i by simpa [a,b,indicator] using hp
   rw [← hf.tsum_eq (fun i hi=>?_)]
   · simp_rw [he]; refine tsum_subtype_eq_of_support_subset (fun i (hi: i∈Function.support b)=>?_)
     change b i≠0 at hi; unfold b at hi; split at hi; swap; · contradiction
     rw [Poly.part_send] at hi; split at hi; next he=> exact he.symm
     contradiction
   change a i≠0 at hi; unfold a at hi; split at hi; swap; · contradiction
   rw [Poly.part_send] at hi; split at hi
   next he=> obtain ⟨i',hV,hZ⟩:= D.lone t U h hv ht he.symm hi; exact ⟨⟨i',hV⟩,Subtype.ext hZ.symm⟩
   contradiction
end Deck
end YM.MergeProof.Ribbons.Fibers
