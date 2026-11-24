import YM.OPE.Compatible.Assemblage.Mirror

/-!
Lift an arc. Add independent slot variables bearing a unit,
not requiring the points thus attached to execute the earlier route.
Actual coefficient identity, not just untagged supplies. Useful to
point a fiber not at any of its previous origins but at its center
of expansion (possibly coincident now).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Mirror
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Stem
open scoped Topology BigOperators Classical
variable {V I J W : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype W][DecidableEq W]{G:Gauge}{n:Side}
    (e:V ↪ W)
def pad (e:V ↪ W)(p:Words V): Words W:= Poly.inject fun i=> p.part (invM e i)
def mark (e:V ↪ W)(i:W):ℂ:= if i∈Set.range e then 0 else 1
lemma installed (p:Words V): pad e p=Poly.pass (Mach (Bud W) (mark e))*rise e p:=by
    let M:=mark e; ext i; rw [Poly.part_mul]; let h:= imageM e (invM e i); let q:Mode W:=⟨i.val\h.val,mem_univ _⟩; have hv(z:W): z∈h.val↔ z∈i.val∧ z∈Set.range e:=by
       constructor
       · intro hz; obtain ⟨u,h,rfl⟩:= mem_image.mp (show z∈h.val from hz); exact ⟨(low_read ..).1 h,Set.mem_range_self _⟩
       rintro ⟨hz,u,hu⟩; subst z; exact mem_image_of_mem _ ((low_read ..).2 hz)
    have hx : h.val ⊆ i.val:= fun z hz=> (hv z|>.1 hz).1
    have he:Poly.merges q h i :=by refine ⟨?_,?_⟩; exact disjoint_sdiff_self_left; exact sdiff_union_of_subset hx
    let f(j k:Mode W):= if Poly.merges j k i then (∏ x∈j.val,M x)*(rise e p).part k else 0
    have hz(j k)(hf:f j k≠0): j=q∧ k=h:=by
       unfold f at hf; split at hf; swap; · contradiction
       next hw=>
       have hs:= hw.2; have hJ (x)(hp:x∈j.val):x∉Set.range e:=fun he=>hf ((mul_eq_zero).mpr (Or.inl (prod_eq_zero hp (if_pos he))))
       have hk: warm e k:=Classical.byContradiction fun hpk=> hf (mul_eq_zero.mpr (Or.inr (no_rise e p k hpk)))
       have hK : k=h:=by
          apply Subtype.ext; ext x; rw [hv]; constructor
          · intro hz; exact ⟨hs ▸ mem_union_right _ hz,(heat_iff e _).1 hk _ hz⟩
          rintro ⟨hz,hQ⟩; exact (mem_union.mp (hs.symm ▸ hz)).resolve_left fun hv=> hJ x hv hQ
       refine ⟨Subtype.ext (by
          ext x; change _ ↔ x∈i.val\h.val; rw [Finset.mem_sdiff,← hs,mem_union,← hK]; constructor
          · intro h; exact ⟨Or.inl h,fun hx=>disjoint_left.mp hw.1 h hx⟩
          rintro ⟨h,hv⟩; exact h.resolve_right hv),hK⟩
    change p.part (invM e i)=_; simp_rw [Mach,pass_fire]; change _=∑ j,∑ k,f j k
    rw [sum_eq_single q,sum_eq_single h]
    · unfold f; rw [if_pos he,rises, show ∏ x∈q.val, M x=1 from ?_,one_mul];
      apply prod_eq_one; intro z h; obtain ⟨hp,h⟩:= Finset.mem_sdiff.mp h; exact if_neg fun he=>h ((hv z).mpr ⟨hp,he⟩)
    · exact fun j _ hp=> not_not.mp fun hf=> hp ((hz _ _ hf).2)
    · simp
    · exact fun j _ hp=> sum_eq_zero fun k _=> not_not.mp fun hf=>hp ((hz _ _ hf).1)
    simp
lemma top_fit {f:Config G n→ Words V}{o:V→Site n}{o':W→ Site n}{s:Support n}{τ:ℝ} (hf:Borne o s f τ)(hp:o'∘e=o) : Borne o' s (rise e ∘ f) τ:=by
    refine ⟨fun _ _ ha hv=> congr_arg (rise e) (hf.home _ _ ha hv),fun y U=> congr_arg (rise e) (hf.turns y U),fun i=>?_,fun U i hi=>?_⟩
    · change Measurable (fun U=> if warm e i then _ else _); split; exact hf.me _; exact measurable_const
    by_contra he; change (rise e (f U)).part i≠0 at he; have hz : warm e i:= Classical.byContradiction fun h=> he (no_rise e _ _ h)
    have hv' := hf.place (invM e i) U (fun h=> he (by change ite (warm e i) _ _=0; rw [if_pos hz]; exact h))
    apply hi; intro a ha; obtain ⟨b,hb,rfl⟩:= mem_image.mp (show a∈(imageM e (invM e i)).val from hz.symm ▸ ha); change (o'∘e) b∈s; exact (congr_fun hp b).symm ▸ (hv' (mem_image_of_mem _ hb))
lemma buses {f:Config G n→Words V}{o:V→Site n}{o':W→ Site n}{s}{t:ℝ}(h:Burns o s f t)(hp:o'∘e=o): Burns o' s (rise e∘f) t:=⟨top_fit e h.toBorne hp,fun U hi=>h.permits U (fun he=> hi (by rw [comp_apply,he,map_zero])),fun U=>(congr_arg (fun i=>(rise e (f U)).part i) (heat_quiet e).symm).trans ((rises e _ _).trans (h.sil _))⟩
lemma flows {f:Config G n→Words V}{o:V→Site n}{o':W→ Site n}{s}{t:ℝ}(h:Accent.Flow o s f t)(hp:o'∘e=o): Accent.Flow o' s (rise e∘f) t:=⟨top_fit e h.toBorne hp,fun U hi=>h.permits U (fun he=> hi (by rw [comp_apply,he,map_zero]))⟩
lemma high_towed {Q X:Type*}{v:V→ℝ}{w:W→ℝ}{S:Q→Support n}{F:Q→X→ Words V}{b:ℕ}{t u:ℝ} (h:Towed v S F b t u)(hp:w∘e=v): Towed w S (fun i=>rise e ∘F i) b t u:=by
   obtain ⟨a,h,hx,hu⟩:=h; refine ⟨a,h,hx,fun i=>?_⟩; obtain ⟨f,hF,hA,ht⟩:= hu i; let l:= fun j=> if warm e j then f (invM e j) else 0
   refine ⟨l,fun j=>?_,fun U j=>?_, le_trans (le_of_eq ?_) ht⟩
   · change 0 ≤ l j; unfold l; split;exact hF _;rfl
   · change ‖ite (warm e j) _ (_ :ℂ)‖ ≤ l j; unfold l; split; exact hA _ _; next=>simp
   unfold wordsPrice; rw [← Finset.sum_subset (subset_univ (univ.image (imageM e))) (fun i _ hn=> ?_),sum_image (LeftInverse.injective (show LeftInverse (invM e) (imageM e) from tall e)|>.injOn)]; apply sum_congr rfl; intro j _; rw [show l _=f j from (if_pos (heat_image e _)).trans (congr_arg f (tall ..)), ← hp]; congr 1; exact prod_image e.injective.injOn
   have hz: ¬ warm e i:=fun he=>hn (show i ∈ univ.image (imageM e) from he ▸ mem_image_of_mem _ (mem_univ _)); exact mul_eq_zero.mpr (Or.inr (if_neg hz))
end YM.MergeProof.Ribbons.ManyCopies.Mirror
