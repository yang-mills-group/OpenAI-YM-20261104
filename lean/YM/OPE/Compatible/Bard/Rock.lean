import YM.OPE.Compatible.Bard.Seats
/-!
# Compute observed signed formula after recombinations.

Confluent slot v remains visible both times. Before, elementary
columns are literal (linear). After, the remainder is literal as
well. Also billing geometry can be read in the same syntax.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells
open scoped Topology BigOperators Classical
variable {X V I G' T W Z: Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype T][DecidableEq T][Fintype W][DecidableEq W]
variable {k i:ℕ}
section
variable [CommMonoid Z] (Q:brim D F⊕ W→ Z)(P:Wave m F K i)
omit [Fintype T][DecidableEq T] in
lemma spur_node (p:T× (brim D F⊕ W)→Z) (x:T)(j:brim D K) : spurs D p P (x,.inl j) = ∏ i∈ (elements D P).contents j,p (x,.inl i):=by
    unfold spurs; change (∏ i∈_,_)=_; let f:brim D F→ (brim D F⊕W):= Sum.inl; have h:(raised W D P).contents (Sum.inl j)=Finset.image f ((elements D P).contents j):=by
       ext u; rw [Fibers.focuses]; cases u
       next i=> exact ⟨fun h=> mem_image_of_mem f (((elements D P).focuses ..).2 (Sum.inl.inj h)), fun h=>congr_arg Sum.inl (((elements D P).focuses ..).1 ((mem_image_of_injective _ Sum.inl_injective).1 h))⟩ -- infer
       next i=> exact ⟨fun h=>False.elim (Sum.inl_ne_inr h.symm),fun h=> False.elim ((mem_image.mp h).elim fun _ ⟨_,h⟩=> Sum.inl_ne_inr h)⟩
    rw [h,prod_image Sum.inl_injective.injOn]
omit [Fintype T][DecidableEq T] in
lemma spur_extra (p:T× (brim D F⊕ W)→Z) (x:T)(j:W): spurs D p P (x,.inr j) = p (x,.inr j):=by
    unfold spurs
    have hp:(raised W D P).contents (Sum.inr j)={Sum.inr j}:=by
       ext i;rw [Fibers.focuses,mem_singleton]; cases i
       next=> exact ⟨fun h=>False.elim (Sum.inl_ne_inr h),fun h=>False.elim (Sum.inl_ne_inr h)⟩
       simp [raised] -- left equations types not rfl
    rw [hp,prod_singleton]
omit [Fintype T][DecidableEq T][DecidableEq W][Fintype W] in
lemma singleton_later (x:brim D K)(i:brim D F)(h:x.val=i.val): (elements D P|>.contents x)={i}:=by
    ext j; rw [Fibers.focuses,mem_singleton]; constructor
    · intro hh; have he:= (P.topper D j x).1 hh; by_contra he'; exact (brim_apart D F P.before.base i.2 j.2 (Subtype.val_injective.ne (Ne.symm he'))) (h ▸ he)
    rintro rfl; exact (P.topper D _ x).2 h.le
-- use products over leaf glen & shore
variable (F) in
def cove (x:X) := (univ:Finset (brim D F)).filter fun i=> x ≤ i.val
lemma elements_bunch (x:brim D K): (elements D P|>.contents x)= cove D F x.val:=by
    ext i; rw [Fibers.focuses,cove, mem_filter,and_iff_right (mem_univ _)]; exact topper D P ..
variable (p:brim D F→ Z)
lemma besides_cove (x:brim D K): (∏ i∈ univ.erase x,∏ j∈ (elements D P).contents i, p j) = ∏ i∈(univ\cove D F x.val),p i:=by
    rw [show univ\cove D F x.val=(univ.erase x).biUnion (elements D P).contents from ?_, prod_biUnion (fun i _ j _ h=>(elements D P).disjoint_c _ _ h)]
    ext i; let Q:=elements D P; let v:= Q.bunch i
    rw [← elements_bunch D P,Finset.mem_sdiff,mem_biUnion,and_iff_right (mem_univ _)]; simp only [Fibers.focuses,exists_eq_right',Finset.mem_erase,and_iff_left (mem_univ _)]
end
end YM.OPE.Arboreal.Arcade
