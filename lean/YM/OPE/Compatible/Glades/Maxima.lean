import YM.OPE.Compatible.Glades.Cluster
/-! Max event gives a true meeting or surviving string. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Series
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open scoped Topology Classical
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X) {Q:Finset X}{m:X→ℕ} (P: Series Q m)
local notation "F" => crease D P
lemma cred (x: after D Q m) : (F).SingleFiber x↔ x.val∉Q:=by
   constructor
   · intro h hv; obtain ⟨a,ha⟩:= chef D P x
     let i:(brim D Q)⊕(buds D Q m):= Sum.inr ⟨x.val,mem_inter.mpr ⟨x.2,hv⟩⟩
     have he:(F).SingleFiber x:=h
     have hh: Sum.inl a =(F).twig x:= ((F).sola _ he (Sum.inl a)).mp ha
     simp [crease,hv] at hh
   intro hx; have ht : (F).twig x= .inl ⟨x.val,spec D P x.2 hx⟩:=dif_neg hx
   unfold Fibers.SingleFiber; rw [ht]; apply Finset.Subset.antisymm
   · intro i hi; have he := ((F).focuses ..).1 hi; rw [mem_singleton]; cases i
     next i=>
        have hv:= (chief_iff D P i x).1 he
        apply congr_arg; apply Subtype.ext; by_contra hh; exact brim_apart D Q P.base (spec D P x.2 hx) i.2 (Ne.symm hh) hv
     next i=> exact False.elim (hx ((congr_arg Subtype.val he) ▸ (mem_inter.mp i.2).2))
   · rw [Finset.singleton_subset_iff]; exact ((F).focuses ..).2 ((chief_iff D P _ x).2 le_rfl)
lemma same (x:after D Q m) (h:(F).SingleFiber x) :∃ a:brim D Q,(F).twig x=.inl a ∧ a.val=x.val:=
    ⟨_,dif_neg ((cred D P x).1 h),rfl⟩
lemma high_node (x: after D Q m)(h:¬ (F).SingleFiber x):x.val∈buds D Q m:= mem_inter.mpr ⟨x.2,not_not.mp ((cred D P x).not.mp h)⟩
include D P
lemma stamp_in (x : brim D Q) (h:¬ (F).SingleFiber ((F).bunch (.inl x))): m (par D x.val)=whenHigh Q m:=by
   let y:= chief D P x; have he:= high_node D P y h; have hh:= reaches D P x; have hz:= birth_stamp D P he; have hi:= (on_brim ..).mp x.2
   have hv:y.val < x.val:=lt_of_le_of_ne hh (fun e=> hi.1 (e ▸ (Finset.mem_inter.mp he).2))
   exact (high D P hi.2.2).antisymm (hz ▸ P.timing y.val _ (touch_par D hv) hi.2.2)
lemma bed_empty (h : ¬ (bed Q m).Nonempty): whenHigh Q m=m ⊥:=by
   apply le_antisymm (le_of_not_gt fun hz=>h ⟨⊥,mem_filter.mpr ⟨P.base.base,hz⟩⟩) (high D P P.base.base)
set_option linter.unusedSectionVars true in
lemma low_bed (h:(bed Q m).Nonempty): whenHigh (bed Q m) m < whenHigh Q m:=by
   cases D
   cases P
   obtain ⟨x,hX,h⟩:=exists_mem_eq_sup _ h m; unfold whenHigh; rw [h]; exact (mem_filter.mp hX).2
end YM.OPE.Arboreal.Series
