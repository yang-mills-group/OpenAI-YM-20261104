import YM.OPE.Compatible.Basil.Gas
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Density
/-!
# On all-good W evaluate conditional normalized Leaf by cut/thin cluster
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Census Itinerary
open Gas Ursell Trees
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (X:Coat T F) (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K)
    (he : RG.flags (Pressure.temp X.x) X.V=∅)
local notation "g" => overhead X R Q.table
local notation "O'" => S.push R.beta R.eval X.V
local notation "Φ" => H.smallAt
local notation "Z" => H.entries X
local notation "R'" => blocked Φ
local notation "P'" => Gas.total R' Z
lemma loanInj : Injective (H.sword):= fun _ _ e=> Finset.map_injective _ e
include hk he in
lemma slogan : g*P'=O':=by
   let f p:=g*ejections R X W o.a Q.halo Q.table p
   have heq p : f (H.sword p)=g*Gas.value R' Z p:=by
     have hh:= H.family_neat X rfl (∅,p)
     rw [Cash.binders] at hh; simp only [Cash.stave,map_empty,empty_union] at hh
     unfold f; rw [← hh]; apply congr_arg
     unfold Cash.inlet Cash.banked Cash.ignores
     dsimp only
     rw [if_pos (show _ =_ by simp [Cash.inventory,he]), show Gas.value _ (H.deposits X) ∅=1 from (by simp [Gas.value,separated])]
     unfold cut; simp [Cash.tall]
   have hp:= loanInj X H -- omit X? H refers
   have hz := (hp.hasSum_iff (f:=f) ?_).2 (real_push X H hk)
   · simp_rw [Function.comp_def,heq] at hz; rw [← hz.tsum_eq,tsum_mul_left];rfl
   intro p hi; unfold f ejections; split
   next hh=>
    suffices h: ∏ i∈p,H.emerging X i=0 by change g*(∏i∈p,H.emerging X i)=_; rw [h,mul_zero]
    by_contra hn
    have hs : ∀ i∈p,(H.unionP i).Nonempty ∧ (roster i).flags=∅:=fun i hi=> by
       obtain ⟨-,-,hv,h⟩:= H.residency X rfl i (fun hp => hn (prod_eq_zero hi hp))
       exact ⟨hv,by rw [h,he]; simp⟩
    exact hi ⟨p.subtype _,by ext; simp [Cash.sword]; grind⟩
   next=> rw [mul_zero]
namespace Leaf
variable (M:Leaf S R)
abbrev umi (M:Leaf S R) (H:Cash W x μ L Q o C T R) (X:Coat T F)(i:H.ThinP):= M.bloom X W o.a Q.table Q.halo i.val
local notation "u" => M.umi H X
lemma bloom_active (hp:M.bloom X W o.a Q.table Q.halo p≠0) : Ac.Spark H.supportP p ∧ troupe T R Q.halo X.B p ∧ M.turn.badge S∈p ∧ enlargement S.ratio Q.halo X.B (RG.inspected M.crest) ⊆ H.unionP p ∧
    (roster p).flags= RG.flags (Pressure.temp X.x) X.V ∩ H.unionP p ∧ (H.unionP p).Nonempty:=by
  have hF : M.turn.badge S∈p:=by by_contra hn; exact hp (M.bloom_off X p hn)
  unfold Leaf.bloom at hp; split at hp; swap; · exact (hp rfl).elim
  next he=>
  have hx : enlargement S.ratio Q.halo X.B (RG.inspected M.crest) ⊆ H.unionP p:=by rw [show enlargement _ _ _ _= areas R T Q.halo X.B (M.turn.badge S) from (M.turn.badge_area ..).symm]; exact subset_biUnion_of_mem _ hF
  refine ⟨he.1,he.2.1,hF,hx,he.2.2.symm,Finset.Nonempty.mono hx ((Finset.Nonempty.image (f:=S.ratio.parent) ?_).mono (halo_subset _ _))⟩
  suffices H : M.crest.Nonempty from H.mono Finset.subset_union_left
  unfold Leaf.crest; cases M.turn
  · exact ⟨_,(R.activities.reg _).anchor⟩
  exact ((R.activities.forced _).inventory_ne).mono (R.activities.forced _).inventory_sup
include he in
lemma conjure (V:Finset H.ThinP): M.froth X W o.a Q.table Q.halo (H.sword V)=consort Φ u Z V:=by
   unfold consort Leaf.froth
   have hp: Matter.covers X (H.sword V):=by
      change _= RG.flags _ _; rw [he]; apply Finset.eq_empty_iff_forall_notMem.mpr; rintro i hi; obtain ⟨j,hj,hi⟩:= mem_biUnion.mp hi; obtain ⟨p,hv,rfl⟩:=mem_map.mp hj; exact Finset.notMem_empty i (p.property.2 ▸ (show i∈(roster p.val).flags from hi))
   let f:H.ThinP ↪ Molecule S:= Embedding.subtype _
   have hs : (∑ i∈ H.sword V,M.bloom X W o.a Q.table Q.halo i*∏ j∈(H.sword V).erase i,proceedsA R X W o.a Q.halo Q.table j)=∑i∈ V,u i*∏ j∈V.erase i,Z j:=by
       unfold Cash.sword; rw [sum_map]; refine sum_congr rfl fun i _hi=> congr_arg (fun y:ℝ=> u i*y) ?_; rw [← Finset.map_erase,prod_map]; rfl
   have hh: (joints T R Q.halo X.B (H.sword V)) ↔ (∀ i∈V,Ac.Spark H.supportP i.val) ∧ separated R' V:=by
       refine ⟨fun ⟨a,b⟩ => ⟨fun i hi=> a (f i) (mem_map_of_mem _ hi),fun i hi j hj h=>not_or_intro h fun ⟨p,hp,hq⟩=> ?_⟩,fun ⟨a,b⟩=> ?_⟩
       · exact Finset.disjoint_left.mp (b (show f i∈H.sword V from mem_map_of_mem _ hi) (show f j∈H.sword V from mem_map_of_mem _ hj) (f.injective.ne h)) hp hq
       refine ⟨fun i hi=>?_,?_⟩; swap
       · intro i hi j hj h; obtain ⟨i,h_i,rfl⟩:=mem_map.mp hi; obtain ⟨j,h_j,rfl⟩:=mem_map.mp hj
         exact Finset.disjoint_left.mpr fun p hp hz=>b i h_i j h_j (fun hn=>h (hn ▸ rfl)) (Or.inr ⟨p,hp,hz⟩)
       obtain ⟨i,h_i,rfl⟩:=mem_map.mp hi; exact a i h_i
   rw [hs]; split_ifs with hx hy
   · rfl
   · exact (hy (hh.mp hx.1).2).elim
   · symm; apply Finset.sum_eq_zero; intro i hi; by_contra hn; apply hx; refine ⟨hh.mpr ⟨?_,by assumption⟩,hp⟩
     intro j hj; by_cases h:j=i
     · subst i; exact (bloom_active X H M (left_ne_zero_of_mul hn)).1
     exact (H.residency X rfl j.val (fun hv=> right_ne_zero_of_mul hn (prod_eq_zero (mem_erase.mpr ⟨h,hj⟩) hv))).1
   rfl
include hk he in
lemma coupon : S.push R.beta M.cicada X.V = g*(∑' s,consort Φ u Z s):=by
   let f p:=g * M.froth X W o.a Q.table Q.halo p
   have h: (f∘ H.sword) = fun v=> g*consort Φ u Z v:=funext fun p=>congr_arg (_*·) (conjure X H he M p)
   have hx := ( (loanInj X H).hasSum_iff (f:=f) ?_).2 (M.streetP X H hk)
   · rw [← hx.tsum_eq,h,tsum_mul_left]
   intro i hi; unfold f Leaf.froth; split
   next hz=>
      rw [show (∑ i'∈i,M.bloom X W o.a Q.table Q.halo i'*∏ v∈i.erase i',proceedsA R X W o.a Q.halo Q.table v)=0 from ?_,mul_zero]; refine Finset.sum_eq_zero fun j hj=> ?_; by_contra hn
      have hs : ∀ k∈i,(H.unionP k).Nonempty ∧ (roster k).flags=∅:=fun k hh=> by
         by_cases h:k=j
         · subst j; obtain ⟨-,-,-,-,hZ,hB⟩:= bloom_active X H M (left_ne_zero_of_mul hn)
           exact ⟨hB,by rw [hZ,he]; simp⟩
         obtain ⟨-,-,hv,h⟩:= H.residency X rfl k (fun hp => right_ne_zero_of_mul hn (prod_eq_zero (mem_erase.mpr ⟨h,hh⟩) hp))
         exact ⟨hv,by rw [h,he]; simp⟩
      exact hi ⟨i.subtype _,by ext; simp [Cash.sword]; grind⟩
   next=> rw [mul_zero]
end Leaf
end YM.PhysicalNext.Repeat.Aroma
