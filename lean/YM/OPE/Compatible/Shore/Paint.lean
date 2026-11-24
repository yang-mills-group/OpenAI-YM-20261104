import YM.OPE.Compatible.Shore.Bay
/-!
# Superposition of exact linear columns through all products
Bud.NILPOTENCE, kill coexisting alternatives on a single slot.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Deb
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem Mirror
open scoped Topology BigOperators Classical
variable {V I J W : Type}[Fintype V][DecidableEq V] [Fintype W][DecidableEq W]{G:Gauge}{n : Side} (f:V→W)(c:V→ℂ)
-- individual mode. Can use arbitrary linear maps single-label to single-label (not wrap several or omit from resulting birth).
abbrev Flat (p:Mode V) : Prop:= Set.InjOn f ↑p.val
def landed (p:Mode V): Mode W:= ⟨p.val.image f,mem_univ _⟩
def sendAll : Words V→ₗ[ℂ] Words W where
    toFun p := Poly.inject fun i=> ∑ j: Mode V, if Flat f j ∧ landed f j=i then (∏ k∈ j.val,c k)*p.part j else 0
    map_add' p q:=by ext i; change (∑ j:Mode V, ite _ _ (_:ℂ))=(∑ j:Mode V, ite (Flat f j ∧ landed f j=i) _ _) + (∑ j:Mode V,ite _ _ (_:ℂ));
                       erw [← sum_add_distrib]; refine sum_congr rfl fun j _=>?_ ; split_ifs; rw [Poly.part_plus,mul_add]; simp
    map_smul' t p:=by ext i; change (∑ j:Mode V, ite _ _ _)= t*(∑ j: Mode V,ite (Flat f j ∧ landed f j=i) _ _); rw [Finset.mul_sum]; refine sum_congr rfl fun j _=>?_ ; split_ifs; rw [Poly.part_smul]; ring; simp
lemma delivered (p:Mode V)(z:ℂ): sendAll f c (Poly.send p z)= if Flat f p then Poly.send (landed f p) ((∏ i∈p.val,c i)*z) else 0:=by
    ext i; change (∑ j: Mode V, ite (Flat f j ∧ landed f j=i) _ _)= _
    rw [sum_eq_single p _ (by simp)]; swap
    · intro b _ he; rw [Poly.part_send]; split_ifs <;> simp_all
    rw [Poly.part_send]; split
    next h=> rw [if_pos h.1,Poly.part_send,if_pos h.2.symm]; simp
    next h=> split; next hh=> rw [Poly.part_send,if_neg (fun H=> h ⟨hh,H.symm⟩)]
             rfl
lemma landed_merge {p q r:Mode V} (h:Poly.merges p q r) (hx:Flat f p) (hy:Flat f q) : Poly.merges (landed f p) (landed f q) (landed f r) ↔ Flat f r:=by
   refine ⟨fun he i hi j hj ht=> ?_,fun hp=>⟨?_,?_⟩⟩
   · rw [← h.2] at hi hj; rcases mem_union.mp hi with hi|hi <;>rcases mem_union.mp hj with hj|hj
     · exact hx hi hj ht
     · exact False.elim (disjoint_left.mp he.1 (mem_image_of_mem f hi) (show f i∈_ from ht ▸ (mem_image_of_mem f hj : f j ∈ (landed f q).val)))
     · exact False.elim (disjoint_left.mp he.1 (mem_image_of_mem f hj) (show f j∈_ from ht ▸ (mem_image_of_mem f hi : f i∈(landed f q).val)))
     exact hy hi hj ht
   · apply disjoint_left.mpr; intro a ha hh; obtain ⟨i,hi,rfl⟩:=mem_image.mp ha; obtain ⟨j,hj,he⟩:=mem_image.mp hh
     obtain rfl:=hp (show j∈r.val from h.2 ▸ mem_union_right _ hj) (show i∈r.val from h.2 ▸ mem_union_left _ hi) he; exact disjoint_left.mp h.1 hi hj
   change (p.val.image f)∪q.val.image f=r.val.image f; rw [← h.2]; exact (image_union ..).symm
lemma deliver_mul (p q:Words V): sendAll f c (p*q)= sendAll f c p * sendAll f c q:=by
   rw [← Poly.studs p,← Poly.studs q,sum_mul,map_sum,map_sum,map_sum,sum_mul]; refine sum_congr rfl fun i _=>?_ ; rw [mul_sum,map_sum,delivered,mul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [delivered]
   let a:=p.part i; let b:=q.part j
   by_cases he: Disjoint i.val j.val
   · let r:Mode V:= ⟨i.val∪j.val,mem_univ _⟩; have h: Poly.merges i j r := ⟨he,rfl⟩; rw [tagged_mul _ _ _ h,delivered]
     split
     next hx=>
        have hI:Flat f i:= hx.mono (by exact_mod_cast show i.val ⊆ r.val from subset_union_left)
        have hJ:Flat f j:= hx.mono (by exact_mod_cast show j.val ⊆ r.val from subset_union_right)
        rw [if_pos hI,if_pos hJ,tagged_mul _ _ _ ((landed_merge f h hI hJ).mpr hx)]
        unfold r; rw [prod_union he]; ring_nf
     next hx=>
        split
        next hi=> split; next hj=>
                     symm; by_contra hb; obtain ⟨y,hv⟩:=(merges_of_tagged_mul hb)
                     have hz: Poly.merges (landed f i) (landed f j) (landed f r):=⟨hv.1,(image_union ..).symm⟩; exact hx ((landed_merge f h hi hj).1 hz)
                  next=> rw [mul_zero]
        next=> rw [zero_mul]
   rw [show Poly.send i a*Poly.send j b=0 from Classical.byContradiction (fun ht=>he (merges_of_tagged_mul ht).choose_spec.1),map_zero]; split
   next hi=>
      split
      next ht=>
             symm; by_contra hp; apply he; have hv := (merges_of_tagged_mul hp).choose_spec.1; exact disjoint_left.mpr fun _ hu hv'=> disjoint_left.mp hv (mem_image_of_mem f hu) (mem_image_of_mem f hv')

      next => rw [mul_zero]
   next=> rw [zero_mul]
lemma deliver_one : sendAll f c 1=1:=by
   change sendAll _ _ (Poly.send (Bud V).quiet 1)=_; rw [delivered,if_pos (show Flat f (Bud V).quiet from fun i hi=> by simp [Census.quiet] at hi), show landed f (Bud V).quiet=(Bud W).quiet from Subtype.ext (image_empty ..), show ∏ i∈(Bud V).quiet.val,c i=1 from prod_empty, mul_one]; rfl
lemma deliver_zero (p:Words V): (sendAll f c p).part (Bud W).quiet=p.part (Bud V).quiet:=by
   change ∑ j: Mode V, ite (Flat f j ∧ landed f j=(Bud W).quiet) _ _= _ -- no outer?
   rw [sum_eq_single (Bud V).quiet]
   · rw [if_pos ⟨fun i hi=> by simp [Census.quiet] at hi,Subtype.ext (image_empty ..)⟩, show ∏ i∈(Bud V).quiet.val,c i=1 from prod_empty, one_mul]
   · intro b _ he; split
     next hp=> have hg:=hp.2; exact False.elim (he (Subtype.ext (image_eq_empty.mp (congr_arg Subtype.val hg))))
     rfl
   simp
lemma deliver_pass (p:Words V)(h:p.part (Bud V).quiet=0): sendAll f c p.pass = Poly.pass (sendAll f c p):= passM (sendAll f c) (deliver_one ..) (deliver_mul f c) p h ((deliver_zero ..).trans h)
end YM.MergeProof.Ribbons.ManyCopies.Deb
