import YM.OPE.Grouping.River

/-!
# Freeze unchanged singleton sectors during group projection

Adapts the reconstruction for the quiet coefficient in Grouping/Ebb. Here, even
for a singleton, use all footprints; a mark can be on a region, not only a K
activity. Removing the constant pepper on the frozen lanes is important because
otherwise that region could intersect a flag, contributing spurious force and
losing the mark's propagation path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] [DecidableEq I][DecidableEq J]
    {n:Side}{G:Gauge}{B:Census V}
variable {X₀ : Type*} [Fintype X₀][DecidableEq X₀] {Δ : Fibers X₀ V}
/-- output slot is kept as one singleton -/
def Only (Δ:Fibers X₀ V) (v:V) : Prop := Δ.contents v={Δ.twig v}
namespace Only
variable {v:V}(h:Δ.Only v)
include h
omit [Fintype V] [DecidableEq X₀] in
lemma again {k:X₀} (hx : k ∈ Δ.contents v): k=Δ.twig v := mem_singleton.mp (show k∈{Δ.twig v} from h ▸ hx)
lemma one : Δ.plena ((Bud V).fire v)=(Bud X₀).fire (Δ.twig v):= by
   apply Subtype.ext; change ({v}:Finset V).biUnion _=_; rw [singleton_biUnion]; exact h
lemma covers : Δ.span ((Bud X₀).fire (Δ.twig v))=(Bud V).fire v:= h.one ▸ Δ.reband _
end Only
namespace Deck
variable (D:Deck V X₀ Δ I J G n) (t:ℝ) (h:D.Wet t) (v:V) (hp:Δ.Only v)
include hp
lemma narrow (p:D.Ink)(hf:D.quip (.inr p)=(Bud V).fire v): p.val.biUnion (fun i=>(D.mode_ i).val)={Δ.twig v}:=
   congr_arg Subtype.val (show D.plank (.inr p) = (Bud X₀).fire _ from (D.run (.inr p)|>.ready).trans ((congr_arg Δ.plena hf).trans hp.one))
lemma one_mark (p:D.Ink)(hf:D.quip (.inr p)=(Bud V).fire v):
    ∃ a∈p.val,(D.mode_ a)=(Bud X₀).fire (Δ.twig v) ∧ ∀ i∈p.val,i≠a → D.roster i=∅:=by
   have hx:= D.narrow v hp p hf
   obtain ⟨a,ha,hv⟩:=mem_biUnion.mp (show Δ.twig v∈p.val.biUnion _ from hx.symm ▸ mem_singleton_self _)
   refine ⟨a,ha,Subtype.ext ?_,fun i hi he=>?_⟩
   · exact eq_singleton_iff_unique_mem.mpr ⟨hv,fun j hj=>mem_singleton.mp (hx ▸ mem_biUnion.mpr ⟨_,ha,hj⟩)⟩
   unfold roster Fibers.span; dsimp only; have hh:(D.mode_ i).val=∅:= by
      apply eq_empty_of_forall_notMem; intro j hj
      have hs:j=Δ.twig v:= mem_singleton.mp (hx ▸ mem_biUnion.mpr ⟨i,hi,hj⟩)
      exact Finset.disjoint_left.mp (p.property.buys.1 hi ha he) hj (hs.symm ▸ hv)
   rw [hh,image_empty]
omit hp in
lemma graphic (p:D.Ink) (i j:I⊕J) (h:∀ x∈p.val,x≠i→ D.roster x=∅) (hx:Collide.link D.kiln.mention p.val i j) : j=i:=by
   induction hx with
   | refl=>rfl
   | @tail k j _ h₁ _=> by_contra he; obtain ⟨_,h',q,_,hq⟩:=h₁; exact notMem_empty q (h j h' he ▸ (show q∈D.roster j from hq))
omit hp in
lemma mandatory (p:D.Ink) {i:I⊕J}(hi:i∈p.val)(h:∀ x∈p.val,x≠i→D.roster x=∅): D.kiln.dirty i:=by
   obtain ⟨j,-,hd,hq⟩:= (D.kiln.takes_mole p.property.fire hi).1 (D.blot _ p.property.wet)
   exact (graphic D p i j h hq) ▸ hd
include h
variable {v}
variable (he:∀ i:J,D.mode_ (.inr i)=(Bud X₀).fire (Δ.twig v) → D.cover (.inr i)=(D.spill i).1)
include he
set_option maxHeartbeats 600000 in
omit hp in
lemma unspool (p:D.Ink)(i:J)(hi:Sum.inr i∈p.val)
    (hm:D.mode_ (.inr i)=(Bud X₀).fire (Δ.twig v))(hx:∀ x∈p.val,x ≠ Sum.inr i→D.roster x=∅) : p.val={Sum.inr i}:=by
   refine eq_singleton_iff_unique_mem.mpr ⟨hi, fun k hk =>?_⟩
   induction p.property.fire.2 _ hi k hk with
   | refl=>rfl
   | @tail k j _ h₁ ih=>
      have hk:= ih h₁.1; obtain ⟨-,hj,c,h1,h2⟩:=h₁; subst k
      by_contra hz; have ht:= hx j hj hz
      rcases j with i'|j
      · obtain ⟨b,hb⟩:=h.clean i'; exact notMem_empty _ (ht ▸ (show Δ.bunch b∈D.roster (.inl i') from mem_image_of_mem Δ.bunch hb))
      rcases c with c|c
      · exact notMem_empty _ (ht ▸ (show c∈D.roster _ from (D.kiln.fuel_left).mp h2))
      have hI:c∈(D.spill i).1:= he i hm ▸ (((D.kiln.fuel_right).mp h1).2 : c∈D.cover (.inr i)); have hJ:c∈(D.spill j).1:= h.plain j ht ▸ (((D.kiln.fuel_right).mp h2).2 : c∈D.cover (.inr j))
      exact disjoint_left.mp (p.property.old (mem_toRight.mpr hi) (mem_toRight.mpr hj) (fun h=>hz (congr_arg _ h.symm))) hI hJ
-- omit unusedSectionVars
variable (U:Config G n)(hv:∀ i:I,D.mode_ (.inl i)=(Bud X₀).fire (Δ.twig v) → D.ash i→ D.toll (.inl i) U=0)
include hv
lemma quiet_branch (p:D.Ink)(hf:D.quip (.inr p)=(Bud V).fire v)(hq:D.nectar t U p≠0):∃ i:J,D.mode_ (.inr i)=(Bud X₀).fire (Δ.twig v) ∧ p.val={Sum.inr i}:=by
   obtain ⟨a|a,ha,hm,hx⟩:= D.one_mark _ hp p hf
   · have ht:=hv a hm (D.mandatory p ha hx); exact False.elim (hq (by unfold nectar bud; split; exact prod_eq_zero ha ht; rfl))
   exact ⟨a,hm,D.unspool _ h he p a ha hm hx⟩
omit hv h he in
lemma admits_one (i:J)(hm:D.mode_ (.inr i)=(Bud X₀).fire (Δ.twig v)): D.Tank {Sum.inr i}:=by
    refine { old:= (?_), buys:= fits_singleton _ _, ready:= ?_, fire:= ⟨singleton_nonempty _,fun a ha b hb=> by rw [mem_singleton.mp ha,mem_singleton.mp hb]; exact .refl⟩, wet:=⟨i,mem_toRight.mpr (mem_singleton_self _)⟩ }
    · have hp : toRight ({Sum.inr i}:Finset (I⊕J))={i}:=by ext; simp
      simp [hp]
    have he': unionTag D.mode_ _ (fits_singleton _ (Sum.inr i)) = (Bud X₀).fire (Δ.twig v):= by
       apply Subtype.ext; change ({Sum.inr i}:Finset (I⊕J)).biUnion _=_; rw [singleton_biUnion,hm]
    change Fibers.Pays _ (unionTag ..); rw [he']; unfold Pays; rw [hp.covers,hp.one]
omit hv in
lemma money (p:D.Ink)(i:J)(hm:D.mode_ (.inr i)=(Bud X₀).fire (Δ.twig v))(hx:p.val={Sum.inr i}) :
    D.fuse p.val=D.spill i ∧ D.quip (.inr p)=(Bud V).fire v ∧ D.nectar t U p=D.toll (.inr i) U:=by
    have hr: D.reach p.val=(D.spill i).1:=by simp [reach,hx,he i hm]
    have ht: D.stain p.val=(D.spill i).2:=by unfold stain; rw [show p.val.toRight={i} from (by rw [hx];ext; simp)]; simp
    refine ⟨Prod.ext hr ht,Subtype.ext ?_,?_⟩
    · rw [paint,(show D.glyph (.inr p)={Sum.inr i} from hx), singleton_biUnion]; change (Δ.span (D.mode_ (.inr i))).val=_; rw [hm,hp.covers]
    unfold nectar; rw [hr,ht]; split
    · unfold bud; rw [(show D.glyph (.inr p)={Sum.inr i} from hx)]; simp
    next hh=> exact (Classical.byContradiction (fun hu=> hh (h.allows i U hu))).symm
open Set Ac Push.Local Push.GridApprox.Nil
variable [Fintype I][Fintype J]
lemma candle (z:Box n):
    (cram (fun i:D.Ink=>D.fuse i.val) (fun i=>Poly.send (D.quip (.inr i)) (D.nectar t U i)) z).part ((Bud V).fire v) =
      (cram D.spill (fun i=>Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)) z).part ((Bud X₀).fire (Δ.twig v)):=by
   let a:=fun i:D.Ink=> if D.fuse i.val=z then (Poly.send (D.quip (.inr i)) (D.nectar t U i)).part ((Bud V).fire v) else 0
   let b:=fun i:J=>if D.spill i=z then (Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)).part ((Bud X₀).fire (Δ.twig v)) else 0
   let r:={i:J|D.mode_ (.inr i)=(Bud X₀).fire (Δ.twig v)}; let f (i:r) : D.Ink:=⟨{Sum.inr i.val},D.admits_one hp _ i.property⟩
   have hf: Injective f:= fun i j he=> Subtype.ext (Sum.inr.inj (Finset.singleton_inj.mp (congr_arg Subtype.val he)))
   have ht(i:r): a (f i)=b i.val:=by
      have hQ:= D.money _ h hp he U (f i) _ i.property rfl; unfold a b; rw [hQ.1,hQ.2.1,hQ.2.2,(show D.mode_ (.inr i.val)=(Bud X₀).fire (Δ.twig v) from i.property)]; simp [Poly.part_send]
   unfold cram; rw [Poly.share (hs:=Summable.of_finite),Poly.share (hs:=Summable.of_finite)];
   erw [_root_.tsum_subtype {i:D.Ink|D.fuse i.val=z} (fun i=> (Poly.send (D.quip (.inr i)) (D.nectar t U i)).part ((Bud V).fire v)),_root_.tsum_subtype {i:J|D.spill i=z} (fun i=>(Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)).part ((Bud X₀).fire (Δ.twig v)))]
   suffices hp:(∑' i,a i)=∑' i,b i by simpa [a,b,indicator] using hp
   rw [← hf.tsum_eq (fun i hi=>?_)]
   · simp_rw [ht]; refine tsum_subtype_eq_of_support_subset (fun i (hi: i∈Function.support b)=>?_) -- hf.tsum
     change b i≠0 at hi; unfold b at hi; split at hi; swap; · contradiction
     rw [Poly.part_send] at hi; split at hi; next he=> exact he.symm
     contradiction
   change a i≠0 at hi; unfold a at hi; split at hi; swap; · contradiction
   rw [Poly.part_send] at hi; split at hi
   next hq=> obtain ⟨i',hV,hZ⟩:= D.quiet_branch _ h hp he U hv i hq.symm hi; exact ⟨⟨i',hV⟩,Subtype.ext hZ.symm⟩
   contradiction
end Deck
namespace Salt
variable (Z:Salt V X₀ Δ G n)(t:ℝ) (U:Config G n) (h:Z.Breeze t) {v:V}(hp:Δ.Only v)
local notation "P"=> Z.vessel t
include hp
private lemma keeps {s:Support n} {q:(Bud X₀).Mode} (hx:q=(Bud X₀).fire (Δ.twig v))(hh:q.val.image Z.grain⊆s): Z.kiln s q=s:=by
    unfold kiln; rw [union_eq_left]; rw [hx,hp.covers]; rw [hx] at hh; exact (by change ({v}:Finset V).image _ ⊆ _; simpa [Salt.focus,Census.fire] using hh)
include h
lemma only_soil (z:Box n)(hz:Z.pepper (Δ.twig v)=0): (Z.soil t z U).part ((Bud V).fire v)=(Z.river z U).part ((Bud X₀).fire (Δ.twig v)):=by
    have he (i: Z.Brook)(h: (P).mode_ (Sum.inr i)=(Bud X₀).fire (Δ.twig v)): (P).cover (.inr i)=((P).spill i).1:=keeps Z hp h i.property.2 -- t unused?
    apply ((P).candle t (Z.wet _ h) hp he U ?_ z).trans (congr_arg (fun p:Poly (Bud X₀)=> p.part ((Bud X₀).fire (Δ.twig v))) (Z.fieldSpend _ U h _))
    rintro ⟨a|a,c⟩ hq hi
    · have hk: a=Δ.twig v:=Finset.singleton_inj.mp (congr_arg Subtype.val hq); change Z.bud _ U _=0; unfold Salt.bud; split; next=> change Z.pepper a=0; rw [hk,hz]
      rfl
    have heq: Z.kiln (Z.leaf (Sum.inr a)) (Z.marker (Sum.inr a))= Z.leaf (Sum.inr a):= Z.keeps hp hq (Z.sits _).2
    by_contra H; have hm' : ¬ Disjoint ((P).cover (.inl (Sum.inr a,c))) (flags t U):= (Z.wet _ h).resid _ U hi H
    have hC:Healthy t (Z.leaf (Sum.inr a)) U:= by
       apply (h.home a.val.1).permits; intro h₁; apply H; change Z.bud _ _ _ = _; unfold Salt.bud; split; change (Z.air _ U).part _=0; rw [h₁,Poly.part_nil]; rfl
    rw [show (P).cover (.inl (Sum.inr a,c))=_ from heq] at hm'; exact hm' hC
end Salt
end YM.MergeProof.Ribbons.Fibers
