import YM.OPE.Compatible.Yolk.Talk
/-!
# Restricted fibres exact K merger. Nothing requiring disjoint flags tests after T(U) etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L₀ : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {X Y:Support f}
abbrev BitScope (A:Activities G f)(Y:Support f)(i:Finset ℕ) := {b : Finset ℕ// towY A Y b=i}
section
variable (A:Activities G f)
abbrev Dorm (A:Activities G f)(Y:Support f):= {b:Finset ℕ // ∀ j∈b,Disjoint (A.forced j).support Y}
lemma slither (b : Dorm A Y){i:Finset ℕ}(h:towY A Y i=i): towY A Y (b.val ∪ i)=i∧Disjoint b.val i:=by
   refine ⟨?_,?_⟩
   · unfold towY; rw [filter_union,show b.val.filter _=∅ from ?_, show i.filter _ =_ from h,empty_union]
     refine Finset.eq_empty_iff_forall_notMem.mpr fun i hi=>?_ ; obtain ⟨h₁,h₂⟩:=mem_filter.mp hi; exact h₂ (b.property i h₁)
   exact Finset.disjoint_left.mpr fun j hj hk=> (mem_filter.mp (show j∈towY A Y i from by rw [h]; exact hk)).2 (b.property j hj)
def shone (i:Finset ℕ)(h:towY A Y i=i):Dorm A Y ≃ BitScope A Y i where
 toFun b:=⟨b.val ∪ i,(slither A b h).1⟩
 invFun b:=⟨b.val \ i,fun j hj=>by obtain ⟨hv,hj⟩:=mem_sdiff.mp hj; by_contra hp; exact hj (by rw [←b.property]; exact mem_filter.mpr ⟨hv,hp⟩)⟩
 left_inv b:=by
   have ht:= (slither A b h).2; apply Subtype.ext; dsimp only
   ext j; constructor
   · intro hi; obtain ⟨hj,hk⟩:=mem_sdiff.mp hi; exact Or.resolve_right (mem_union.mp hj) hk
   intro hi; exact mem_sdiff.mpr ⟨mem_union_left _ hi,fun hh=> Finset.disjoint_left.mp ht hi hh⟩
 right_inv b:=by
   apply Subtype.ext; dsimp only; apply Finset.sdiff_union_of_subset; exact b.property.symm.trans_le (filter_subset ..)
end
section
variable {h: Config G f → ℝ} {i:Finset ℕ} {k:ℕ}
variable (L:Leaf S R) (he:L.turn=.gasKey k)(h₁:(R.activities.forced k).support=enrolY R.activities Y i)
 (h₂:(R.activities.forced k).inventory= groupY R.activities i)(hL:L.ingredient=court R Y i h)
 (hv:R.activities.Valid R.p σ w) (hY:Y.Nonempty)(hs:towY R.activities Y i=i)
local notation "A" => R.activities
set_option quotPrecheck false
local notation "Ξ" => (fun i=> (R.activities.forced i).support)
local notation "Ya" => enrolY A Y i
include h₁ hY
private lemma k_out (p:Dorm R.activities Y):k∉ p.val:=fun hj=> by have he:= p.property k hj; rw [h₁] at he; obtain ⟨i,hv⟩:=hY; exact Finset.disjoint_left.mp he (mem_union_left _ hv) hv
include L he h₂ hL hs
lemma glue_Y (b:Dorm R.activities Y)(U:Config G f) : L.bun (insert k b.val) U= h U*R.activities.gasOccurrence R.p (b.val ∪ i) U:=by
   unfold Leaf.bun Leaf.bill Activities.gasOccurrence
   have hk:k∉b.val:= k_out h₁ hY b
   obtain ⟨hH,hJ⟩:= slither A b hs
   have h:((A).admissible R.p U (b.val∪i)) ↔ ((A).admissible R.p U (insert k b.val))∧ (i:Set ℕ).PairwiseDisjoint Ξ:=by
      have hi₀:(insert k b.val).biUnion (fun i=>((A).forced i).inventory)=(b.val∪i).biUnion (fun i=>((A).forced i).inventory):=by rw [biUnion_insert, union_biUnion,h₂, union_comm]
      constructor
      · rintro ⟨ha,hb⟩
        have hp : ∀ y∈b.val,Disjoint (Ξ y) Ya:=by
           intro y hy; apply Finset.disjoint_left.mpr; intro j hj hx; rcases mem_union.mp hx with hg|hg
           · exact Finset.disjoint_left.mp (b.property y hy) hj hg
           obtain ⟨u,hu,hg⟩:=mem_biUnion.mp hg; exact Finset.disjoint_left.mp (ha (mem_union_left i hy) (mem_union_right b.val hu) (fun h=> Finset.disjoint_left.mp hJ hy (h.symm ▸ hu))) hj hg
        refine ⟨⟨?_,hi₀.trans hb⟩,fun j hj u hu=>ha (mem_union_right b.val hj) (mem_union_right b.val hu)⟩
        intro j hj u hu ht
        change Disjoint (Ξ j) (Ξ u); dsimp only
        rcases mem_insert.mp hj with h_j|h_j <;> rcases mem_insert.mp hu with h_u|h_u
        · exact (ht (h_j.trans h_u.symm)).elim
        · rw [h_j,h₁]; exact (hp u h_u).symm
        · rw [h_u,h₁]; exact hp j h_j
        exact ha (mem_union_left _ h_j) (mem_union_left _ h_u) ht
      rintro ⟨⟨ha,hb⟩,hd⟩
      have hp : ∀ y∈b.val,∀ j∈i, Disjoint (Ξ y) (Ξ j):=by
        intro y hy j hj
        have he':Disjoint (Ξ y) (Ξ k):= ha (mem_insert_of_mem (b:=k) hy) (mem_insert_self _ _) (fun h=>hk (h ▸ hy))
        apply he'.mono_right
        dsimp only; rw [h₁]
        exact fun i hi=>mem_union_right _ (mem_biUnion.mpr ⟨j,hj,hi⟩)
      refine ⟨?_,hi₀.symm.trans hb⟩; intro j hj u hu ht
      rcases mem_union.mp hj with hj|hj<;> rcases mem_union.mp hu with hu|hu
      · exact ha (mem_insert_of_mem (b:=k) hj) (mem_insert_of_mem (b:=k) hu) ht
      · exact hp j hj u hu
      · exact (hp u hu j hj).symm
      exact hd hj hu ht
   rw [h]; by_cases hm:(A).admissible R.p U (insert k b.val); swap
   · simp only [hm,false_and,mul_zero,↓reduceIte]
   rw [if_pos hm,he,if_pos (show Wing.Occupied (.gasKey k) _ from mem_insert_self ..), Wing.remaining,Finset.erase_insert hk,hL]; unfold court; rw [hm.2.symm,biUnion_insert,h₂]
   -- flags ∩= identity iff all K in b supports true by hm including no intersections; no extraTests needed
   have hp : groupY A i ⊆ Ya:=fun l hl=>by obtain ⟨j,hj,hq⟩:=mem_biUnion.mp hl; exact mem_union_right _ (mem_biUnion.mpr ⟨j,hj,((A).forced j).inventory_sup hq⟩)
   have hh' : Disjoint Ya (b.val.biUnion (fun j=>((A).forced j).inventory)):=by
     apply Finset.disjoint_left.mpr; intro y hy hz; obtain ⟨j,hj,hz⟩:=mem_biUnion.mp hz; exact Finset.disjoint_left.mp
       (hm.1 (mem_insert_self ..) (mem_insert_of_mem (b:=k) hj) (fun h'=>hk (h'.symm ▸ hj))) (h₁.symm ▸ hy) (((A).forced j).inventory_sup hz)
   have ht₀ : Ya ∩ (groupY A i ∪ b.val.biUnion (fun i=>(R.activities.forced i).inventory)) = groupY A i := by rw [Finset.inter_union_distrib_left,inter_eq_right.mpr hp, disjoint_iff_inter_eq_empty.mp hh',union_empty]
   by_cases he':(i:Set ℕ).PairwiseDisjoint Ξ
   · rw [if_pos ⟨he',ht₀⟩,if_pos ⟨hm,he'⟩,prod_union hJ]; ring
   rw [if_neg (fun hh=>he' hh.1),if_neg (fun hh=>he' hh.2),zero_mul,mul_zero]
lemma filled (U:Config G f): L.cicada U = Real.exp (R.exponent U) * ∑' a : BitScope A Y i,h U*R.activities.gasOccurrence R.p a.val U:=by
   unfold cicada; apply congr_arg; let J (j:Dorm A Y):= insert k j.val; have heq j:=glue_Y L he h₁ h₂ hL hY hs j U
   have ha : Injective J:= fun a b hh=> Subtype.ext (by have hx:= congr_arg (fun s:Finset ℕ=> s.erase k) hh; unfold J at hx; rw [erase_insert (k_out h₁ hY a),erase_insert (k_out h₁ hY b)] at hx; exact hx)
   rw [← (shone A i hs).tsum_eq, ← ha.tsum_eq ?_]; swap
   · intro j hj; change L.bun j U≠0 at hj; unfold Leaf.bun at hj;split at hj; swap;· exact (hj rfl).elim
     next hQ=>
      unfold Leaf.bill at hj; rw [he] at hj; split at hj
      next hh=>
        refine ⟨⟨j.erase k, fun u hu=>?_⟩,insert_erase (show k∈j from hh)⟩
        have hz:Disjoint ((A).forced u).support ((A).forced k).support:= hQ.1 (mem_of_mem_erase hu) hh (ne_of_mem_erase hu); rw [h₁] at hz; exact hz.mono_right subset_union_left
      exact (hj rfl).elim
   exact tsum_congr heq
end
end YM.PhysicalNext.Repeat.Aroma
