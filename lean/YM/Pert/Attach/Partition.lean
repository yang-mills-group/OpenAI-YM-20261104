import YM.Pert.Attach.Links

/-! Reindexing exact positive/negative signed words before changing indicators. No independence assumption on activities. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Attach
open Function Lattice Wilson MeasureTheory RG Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {A:Activities G n} {X:Corrections G n} {R:Activities G n} {U:Config G n}
    {t:ℝ} {P:BudgetPoint}
local notation "B!" => attach A X P.threshold R
set_option quotPrecheck false

def flatten (A:Activities G n) (X:Corrections G n) (s:Finset ℕ) := s.biUnion (parts A X)
open Classical in
def start (A:Activities G n) (X:Corrections G n) (p:BudgetPoint) (U:Config G n) (s:Finset Old) :=
    if A.admissible p U s.toLeft then ∏ l∈s, weight A X U l else 0

lemma valid_out {B:Activities G n} {s:Finset ℕ} (h:B.admissible P U s) {i} (hi:i∈s) :
    (B.forced i).support ∩ flags P.threshold U = (B.forced i).inventory := by
   ext x; constructor
   · intro hx; obtain ⟨he,hu⟩ := mem_inter.mp hx
     obtain ⟨j,hj,hj'⟩ := mem_biUnion.mp (h.2.symm ▸ hu)
     by_cases i=j
     · subst j; exact hj'
     exact (disjoint_left.mp (h.1 hi hj (by assumption)) he ((B.forced j).inventory_sup hj')).elim
   intro hx; exact mem_inter.mpr ⟨(B.forced i).inventory_sup hx,h.2 ▸ mem_biUnion.mpr ⟨i,hi,hx⟩⟩

lemma bills_flatten (s:Finset ℕ) : bill A (flatten A X s) = s.biUnion (fun i=>(page A X i).inventory) := by
    simp_rw [show (page A X _).inventory = _ from bill_union (X:=X) ..] -- fix
    rw [bill_union (X:=X)]; unfold flatten; ext x; simp only [mem_biUnion]; tauto

lemma flatten_pairwise {s} (hs:s.Nonempty ∨ True) (h : ((s : Finset ℕ) : Set ℕ).PairwiseDisjoint fun i=> (page A X i).support) :
    ((flatten A X s).toLeft : Set ℕ).PairwiseDisjoint fun i=>(A.forced i).support := by
    intro i hi j hj hE
    obtain ⟨p,hp,hi⟩:= mem_biUnion.mp (mem_toLeft.mp hi)
    obtain ⟨p',hp',hj⟩:= mem_biUnion.mp (mem_toLeft.mp hj)
    by_cases e:p=p'
    · subst p'; exact (decoding A X p).2.2.2 (mem_toLeft.mpr hi) (mem_toLeft.mpr hj) hE
    exact Disjoint.mono (sub_cover_old A X (mem_toLeft.mpr hi)) (sub_cover_old A X (mem_toLeft.mpr hj)) (h hp hp' e)

lemma parts_flatten {s} (hs:(B!).admissible P U s) :
    Ac.Parts (X.area A) (flatten A X s) = s.image (parts A X) := by
    rw [show flatten A X s = (s.image (parts A X)).biUnion id by rw [image_biUnion]; rfl]
    apply Ac.separates
    · intro a ha; obtain ⟨i,hi,rfl⟩:=mem_image.mp ha; exact (decoding A X i).2.1
    intro a ha b hb e; obtain ⟨i,hi,rfl⟩:=mem_image.mp ha; obtain ⟨j,hj,rfl⟩:=mem_image.mp hb
    exact hs.1 hi hj fun p=>e (congr_arg _ p)

lemma flatten_match (Hx:A.ForcedFamily P) {s:Finset ℕ} (hB:(B!).admissible P U s) :
    (B!).gasOccurrence P s U = start A X P U (flatten A X s) := by
    unfold Activities.gasOccurrence start; rw [if_pos hB, if_pos (show A.admissible P U _ from
      ⟨flatten_pairwise (Or.inr trivial) hB.1,(bills_flatten _).trans hB.2⟩)]
    unfold flatten; rw [prod_biUnion ?_]
    · refine prod_congr rfl fun i hi => ?_
      change entry A X _ i U = _
      unfold entry; split_ifs with hg
      · rfl
      symm
      by_contra! hu
      refine hg ⟨valid_out hB hi, fun j hj => (Hx.permit j U ?_).2⟩
      exact fun he=> hu (prod_eq_zero (mem_toLeft.mp hj) he)
    intro i hi j hj e
    by_contra! hh
    obtain ⟨z,hz,hz'⟩:= not_disjoint_iff.mp hh
    by_cases he : (X.area A z).Nonempty
    · obtain ⟨x,hx⟩:=he
      exact disjoint_left.mp (hB.1 hi hj e) (show x∈full A X (parts A X i) from mem_biUnion.mpr ⟨_,hz,hx⟩)
        (show x∈full A X (parts A X j) from mem_biUnion.mpr ⟨_,hz',hx⟩)
    obtain ⟨k,hk⟩ := (decoding A X i).2.2.1
    have hc := (decoding A X i).2.1.2 _ (mem_toLeft.mp hk) _ hz
    generalize hp : z=z' at he hc
    cases hc with
    | refl => exact he ((A.forced k).inventory_ne.mono (A.forced k).inventory_sup)
    | tail _ ha => obtain ⟨-,ha,x,hx,hx'⟩:=ha; exact he ⟨x,hx'⟩

lemma recognized (h:∀ j, Healthy P.threshold (X.region j) U → X.value j U=0) {s} (hs:start A X P U s ≠ 0)
   {q} (hq:q∈Ac.Parts (X.area A) s) : ∃ i,parts A X i=q := by
   obtain ⟨hle,hj⟩:= Ac.lives (X.area A) s hq
   unfold start at hs; split_ifs at hs with had; rotate_left; · contradiction
   have hold : q.toLeft.Nonempty := by
     obtain ⟨i,hi⟩:=hj.1
     cases i with
     | inl i => exact ⟨i,mem_toLeft.mpr hi⟩
     | inr i =>
       obtain ⟨x,hx,hx'⟩:= not_disjoint_iff.mp (show ¬Healthy P.threshold (X.region i) U from
            fun he => hs (prod_eq_zero (hle hi) (h i he)))
       rw [← had.2] at hx'; obtain ⟨k,hk,hx'⟩ := mem_biUnion.mp hx'
       refine ⟨k,mem_toLeft.mpr ?_⟩
       rw [← Ac.contains (X.area A) hq _ hi]
       exact (Ac.bright ..).mpr ⟨mem_toLeft.mp hk,.single ⟨hle hi,mem_toLeft.mp hk,x,hx,(A.forced k).inventory_sup hx'⟩⟩
   let C : Cluster A X := ⟨q,hj,hold, fun i hi j hj=> had.1 (toLeft_subset_toLeft hle hi) (toLeft_subset_toLeft hle hj)⟩
   obtain ⟨r,e⟩ := (decoding A X).surjective C
   exact ⟨r,congr_arg Subtype.val e⟩

lemma split_flatten (h:∀ j, Healthy P.threshold (X.region j) U → X.value j U=0) {s} (hs:start A X P U s ≠ 0) :
   ∃ b, (B!).admissible P U b ∧ flatten A X b = s := by
   let lists := Ac.Parts (X.area A) s
   let f (z : lists) := (recognized h hs z.property).choose
   let b := lists.attach.image f
   have he : b.image (parts A X) = lists := by
     ext i; constructor
     · intro hi; obtain ⟨a,ha,rfl⟩ := mem_image.mp hi; obtain ⟨p,-,rfl⟩ := mem_image.mp ha
       exact ((recognized h hs p.property).choose_spec).symm ▸ p.property
     intro hi
     exact mem_image.mpr ⟨_,mem_image_of_mem f (mem_attach lists ⟨i,hi⟩),(recognized h hs hi).choose_spec⟩
   have ht : flatten A X b = s := by
     rw [show flatten A X b = (b.image (parts A X)).biUnion id by rw [image_biUnion];rfl,he]
     exact Ac.reconstruct (X.area A) s
   refine ⟨b,⟨?_,?_⟩,ht⟩
   · intro i hi j hj hn
     have hmem (a) (ha:a∈b) : parts A X a ∈ lists := he ▸ mem_image_of_mem _ ha
     exact Ac.separate (X.area A) s (hmem i hi) (hmem j hj) (parts_inj A X |>.ne hn)
   change (b.biUnion fun i=>(page A X i).inventory) = _; rw [← bills_flatten,ht]; unfold start at hs; split at hs
   next ha => exact ha.2
   contradiction

lemma gas_matched (Hx:A.ForcedFamily P) (h:∀ j, Healthy P.threshold (X.region j) U → X.value j U=0)
    (R:Activities G n) (z : ℝ) :
    HasSum ((B!).gasOccurrence P · U) z ↔ HasSum (start A X P U) z := by
   let v := ((B!).gasOccurrence P · U)
   let w := start A X P U
   have active (s : Function.support v) : (B!).admissible P U s.val := by
     by_contra! hn
     exact s.property (if_neg hn)
   have he (s : support v) : w (flatten A X s.val) = v s := (flatten_match Hx (active s)).symm
   let f : support v → support w := fun s => ⟨flatten A X s.val, show w _ ≠ 0 from by rw [he s]; exact s.property⟩
   have hi : Injective f := by
     intro s t hst
     apply Subtype.ext; apply image_injective (parts_inj A X)
     rw [← parts_flatten (active s),← parts_flatten (active t), show flatten A X s.val=flatten A X t.val from congrArg Subtype.val hst]
   have ht : Surjective f := by
     intro s; obtain ⟨b,hb,e⟩ := split_flatten (R:=R) h s.property
     exact ⟨⟨b,show v b ≠ 0 from by rw [show v b = _ from flatten_match Hx hb,e]; exact s.property⟩,Subtype.ext e⟩
   exact (Equiv.ofBijective f ⟨hi,ht⟩).hasSum_iff_of_support he
end YM.Pert.Attach
