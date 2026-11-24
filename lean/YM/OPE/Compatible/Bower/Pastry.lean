import YM.OPE.Compatible.Shore.Graft
/-!
# Batch date. Tiny variant of `whenHigh`. Used only when at least one
level remains to the root (before that standard windfall applies).
Either an actual `crest` or waiting exactly a hop; keeps accounting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {X V W:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U Q F K:Finset X}{m:X→ℕ} {n:ℕ}
structure Wave (m:X→ℕ)(F K:Finset X)(n:ℕ) : Prop where
    before : Series F m
    after : Series K m
    next : K⊆F
    lower : whenHigh K m < n
    upper : whenHigh F m ≤ n
    swept a : a∈F\K → m a=n
namespace Wave
def clip (m:X→ℕ)(F:Finset X)(n:ℕ):= F.filter fun i=>m i<n
lemma cut (h:Series F m)(hp:m ⊥< n)(hq: whenHigh F m ≤ n):Wave m F (clip m F n) n:=by
    let T:=clip m F n; have he : ⊥ ∈ T:=mem_filter.mpr ⟨h.base.base,hp⟩; have hv: T⊆ F:= filter_subset ..
    refine ⟨h,⟨⟨he,hv.trans h.base.inner,fun hi hk=>?_⟩,fun x y hx hy=> h.timing x y hx (hv hy)⟩,hv,?_,hq,fun x hx=>?_⟩
    · exact mem_filter.mpr ⟨h.base.roots hi (hv hk),lt_of_le_of_lt (h.timing _ _ hi (hv hk)) (mem_filter.mp hk|>.2)⟩
    · obtain ⟨s,hs,hS⟩:=exists_mem_eq_sup T ⟨_,he⟩ m; change T.sup _< _; rw [hS]; exact (mem_filter.mp hs).2
    obtain ⟨hf,hh⟩:=mem_sdiff.mp hx; exact le_antisymm ((le_sup (f:=m) hf).trans hq) (le_of_not_gt (fun hv=>hh (mem_filter.mpr ⟨hf,hv⟩)))
variable (P:Wave m F K n)
include P D
lemma sweep {v:X}(hv:v∈brim D K)(hf:v∉F) : v∈brim D F:=by
    rw [on_brim] at *; exact ⟨hf,hv.2.1,P.next hv.2.2⟩
lemma ancestor {x:X}(h:x∈brim D F): ∃ a∈brim D K, a≤x:=by
    let G u:=u∉K→∃ a∈brim D K,a ≤ u
    have he : G x:= journey D (P:=G) (fun he=> False.elim (he P.after.base.base)) (fun i hi IH he=> by
       by_cases h:par D i∈ K
       · exact ⟨i,(on_brim ..).2 ⟨he,hi,h⟩,le_rfl⟩
       obtain ⟨a,ha,hq⟩:=IH h; exact ⟨a,ha,hq.trans (par_le ..)⟩) x
    exact he (fun hz=> ((on_brim ..).1 h).1 (P.next hz))
lemma also_down {u:X}(hu:u∈brim D K):∃ x∈brim D F,u≤x:=by
   by_cases he:u∈ F; swap; · exact ⟨_,sweep D P hu he,le_rfl⟩
   suffices h:∀ v∈F,∃ x∈brim D F,v≤x from h u he
   intro v; refine (Finite.wellFounded_of_trans_of_irrefl (α:=X) GT.gt).induction (C:=fun v=>v∈F→∃ x∈brim D F, v≤x) v ?_; intro a ih hz
   obtain ⟨b,hb⟩:= (kids_heart D).2 (P.before.base.inner hz); have hp:= (kid_mem ..).mp hb
   by_cases hB:b∈F
   · obtain ⟨i,hi,hx⟩:= ih b hp.1 hB; exact ⟨i,hi,hp.1.le.trans hx⟩
   exact ⟨b,(on_brim D F).mpr ⟨hB,bot_lt_iff_ne_bot.mp (lt_of_le_of_lt bot_le hp.1),hp.2 ▸ hz⟩,hp.1.le⟩
def topHat (x:brim D F): brim D K:=⟨Classical.choose (ancestor D P x.2),(Classical.choose_spec (ancestor D P x.2)).1⟩
lemma visits (x:brim D F): (topHat D P x).val ≤ x.val:= (Classical.choose_spec (ancestor D P x.2)).2
lemma topper (x:brim D F)(y:brim D K): topHat D P x=y↔y.val ≤ x.val:=by
   refine ⟨fun h=>h ▸ visits D P x,fun he=>?_⟩
   by_contra hp; let v:=topHat D P x; have hh:v.val≠y.val:=Subtype.val_injective.ne hp
   exact (D.path (visits D P x) he).elim (brim_apart D K P.after.base v.2 y.2 hh) (brim_apart D K P.after.base y.2 v.2 hh.symm)
lemma applies (x:brim D K):∃ y:brim D F, topHat D P y=x:=by obtain ⟨v,hv,hq⟩:=also_down D P x.2; exact ⟨⟨v,hv⟩,(topper D P _ x).2 hq⟩
def elements : Fibers (brim D F) (brim D K):= ⟨topHat D P,fun i=>(applies D P i).choose,fun i=>(applies D P i).choose_spec⟩
def starts (F K:Finset X):= F∩brim D K
-- counter slots survive automatically. blank attached. Supports surplus costs not `places X`.
-- before F arm normal brim F plus W extras. blanks play always to normal brimK
variable (W)
def raised : Fibers (brim D F ⊕ W) (brim D K ⊕ W) where
   bunch := Sum.map (topHat D P) id
   twig := Sum.map (elements D P|>.twig) id
   sectioned i:=by cases i; exact congr_arg Sum.inl ((elements D P).sectioned _); rfl
def riseUp : Fibers ((brim D F ⊕ W)⊕(starts D F K)) (brim D K ⊕ W) where
   bunch := Sum.elim ((raised W D P).bunch) fun i=> .inl ⟨i.val,(Finset.mem_inter.mp i.2).2⟩
   twig x := x.elim (fun i=> if h:i.val∈F then Sum.inr ⟨i.val,mem_inter.mpr ⟨h,i.2⟩⟩ else .inl (.inl ⟨i.val,P.sweep D i.2 h⟩)) (fun i=>.inl (.inr i))
   sectioned :=by
      intro i; cases i; next i =>
         dsimp only [Sum.elim]; split; rfl; next h=> exact congr_arg Sum.inl ((topper D P _ i).2 le_rfl)
      rfl
end Wave
end YM.OPE.Arboreal
