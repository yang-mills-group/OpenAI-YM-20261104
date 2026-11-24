import YM.OPE.Compatible.Bower.Pastry
/-!
# Structural access to the wave. Outputs preservation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Wave
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {X V:Type}(W:Type)[PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U Q F K:Finset X}{m:X→ℕ} {n:ℕ}(P:Wave m F K n)
variable [Fintype W] [DecidableEq W]
set_option quotPrecheck false
local notation "R"=> riseUp W D P
lemma solos (x:brim D K): (R).SingleFiber (.inl x) ↔ x.val∉F:=by
    constructor
    · intro h he; obtain ⟨i,hi⟩:= applies D P x; have hl:(R).bunch (.inl (.inl i))=.inl x:= congr_arg Sum.inl hi; have hp := ((R).sola (.inl x) h _).1 hl; rw [show (R).twig (.inl x)=Sum.inr ⟨x.val,mem_inter.mpr ⟨he,x.2⟩⟩ from dif_pos he] at hp; contradiction
    intro he; let a:brim D F:= ⟨x.val,P.sweep D x.2 he⟩; have ht : (R).twig (.inl x)= .inl (.inl a):= dif_neg he; ext j; rw [(R).focuses,mem_singleton,ht]; cases j
    · rename_i p; cases p
      next y=>
        refine ⟨fun he=>congr_arg _ (congr_arg _ ?_),fun hv=>?_⟩
        · by_contra hm; have hv:a.val ≠ y.val:= Subtype.val_injective.ne (Ne.symm hm); exact brim_apart D F P.before.base a.2 y.2 hv ((topper D P y x).1 (Sum.inl.inj he))
        obtain rfl:y=a:= Sum.inl.inj (Sum.inl.inj hv); exact congr_arg Sum.inl ((topper D P a x).2 le_rfl)
      exact ⟨fun h=> by contradiction, fun he=>by injection he with hh; contradiction⟩ -- no unfolded
    next y=>
       refine ⟨fun hh=>?_,fun h=>by contradiction⟩; apply False.elim; apply he; have hv:y.val=x.val:= congr_arg Subtype.val (Sum.inl.inj hh); exact hv ▸ (mem_inter.mp y.2).1
variable {W}
lemma take_left (x:brim D K)(h:(riseUp W D P).SingleFiber (.inl x)) : ∃ a:brim D F, (R).twig (.inl x)= .inl (.inl a) ∧ a.val=x.val:=⟨_,dif_neg ((solos W D P x).1 h),rfl⟩
omit [Fintype W][DecidableEq W] in
lemma take_new (x:brim D K)(h: x.val∈F): (riseUp W D P).twig (.inl x)= .inr ⟨x.val,mem_inter.mpr ⟨h,x.2⟩⟩:=dif_pos h
omit [Fintype W][DecidableEq W] in
lemma take_right (z:W) : (R).twig (.inr z)= .inl (.inr z):= rfl
lemma pilots (z:W): (R).SingleFiber (.inr z):=by
   ext x; rw [(R).focuses,mem_singleton, take_right]; cases x
   next x=> cases x; next=> exact ⟨fun h=>False.elim (Sum.inl_ne_inr h), fun h=>False.elim (Sum.inl_ne_inr (Sum.inl.inj h))⟩
            next a=>change Sum.inr _=Sum.inr _↔_; simp
   exact ⟨fun h=>False.elim (Sum.inl_ne_inr h), fun h=> by contradiction⟩
include D P
lemma taken (x:brim D K)(h:x.val∈F): m x.val=n:= P.swept _ (mem_sdiff.mpr ⟨h,(on_brim ..).mp x.2|>.1⟩)
lemma children (x:brim D F) (h:(P.topHat D x).val∈F): finishAt D m x.val=n:=by
    let t:=P.topHat D x; have ht:= P.taken D t h; obtain ⟨hh,hQ,hR⟩:= (on_brim ..).mp x.2
    exact ((Series.high D P.before hR).trans P.upper).antisymm ((le_of_eq ht.symm).trans (P.before.timing _ _ (touch_par D (lt_of_le_of_ne (P.visits D x) (fun e=>hh (e ▸ h)))) hR))
lemma stand (x:brim D K): finishAt D m x.val < n:= lt_of_le_of_lt (Series.high D P.after ((on_brim ..).mp x.2|>.2.2)) P.lower
lemma coming (x:brim D F): finishAt D m x.val ≤ n := (Series.high D P.before ((on_brim ..).mp x.2|>.2.2)).trans P.upper
lemma upward (h:F⊆U)(N:ℕ)(ht: ∀ i:brim D F,n ≤ roof U m N i.val) (x:brim D K): n ≤ roof U m N x.val:=by
   by_cases he:x.val∈F; · exact le_of_eq ((P.taken D x he).symm.trans (if_pos (h he)|>.symm))
   exact ht ⟨x.val,P.sweep D x.2 he⟩
end YM.OPE.Arboreal.Wave
