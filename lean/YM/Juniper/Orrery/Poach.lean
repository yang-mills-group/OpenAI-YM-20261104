import YM.Juniper.Orrery.Rim
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Slide
open Progress.DirectedRecipe UVExtension Height StressFlux
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {c C:Side} {k:ℕ} {ρ:ℝ} (P:BudgetPoint)
section pricey
variable (B: BudgetPoint) (S:PathData G) {hC:C.val=c.val*k}
    (V:Curtain G c) (T:Curtain G C)
local notation "H"=> (Macrame.splitter (Deck.divides hC))
local notation "F"=> (Macrame.normal (Deck.divides hC) hC)
local notation "L"=> lowEntry G S B
local notation "J"=> highEntry G S
local notation "K"=> Collection.incoming V.book S B
local notation "Q"=> Collection.incoming T.book S B
open Meadow
abbrev peer (hC:C.val=c.val*k){W:Type*}(i:Seat C× W): Seat c × W:= Prod.map (fun u=> Meadow.pinch hC u) id i
include hC
lemma peer_same {W:Type*} (i j:Seat C× W)(h : i.1.2=j.1.2)(ht:peer hC i=peer hC j): i=j:= Prod.ext (Prod.ext (congr_arg (fun p:Seat c× W => p.1.1) ht) h) (congr_arg (fun p:Seat c× W => p.2) ht)
lemma low_site (i : Collection.Faces C) : (lowEntry G S B (peer hC i)).support=((lowEntry G S B i).support.image H):= by
   change (Meadow.pinch hC i.1).spread (Low.home S i.2 B 0) = _
   rw [show (0: Site c)= H 0 from (map_zero ..).symm,Orrery.low_home hC B]; exact spreaded hC ..
lemma high_site (i:Collection.Spikes C): (highEntry G S (peer hC i)).support=((highEntry G S i).support.image H):= by
   let J':=High.term S i.2; change (Meadow.pinch hC i.1).spread (J'.footprint 0) = _
   rw [show (0:Site c)=H 0 from (map_zero ..).symm, Deck.steadied hC]; exact spreaded hC ..
omit hC in
lemma spread_short {Z:Support c}(i:Seat c)(hi:(0:Site c)∈Z): ShortF B.B (i.reg Z hi) ↔ Z ⊆ neighbors B.B 0:=by
   apply Iff.trans (Orrery.short_perm (i:= (⟨(0:Site c),Z,hi⟩: RegularAddress c)) rfl i.turn_zero.symm) Iff.rfl -- included hC unneeded
lemma short_downF (h : Margin B c) (i : Collection.Faces C) : ShortF B.B (L (peer hC i)) ↔ ShortF B.B (L i):= by
   rw [lowEntry,lowEntry,spread_short,spread_short]; constructor -- hC unused?
   · intro hi; apply Orrery.low_rim hC B h S i.snd; intro x hx; apply (neighbors_mem ..).1; refine hi ?_
     change _∈Low.home S i.2 B 0; rw [show (0:Site c)=H 0 from (map_zero ..).symm,Orrery.low_home hC B]; exact mem_image_of_mem _ hx
   intro hp x hx; change x∈Low.home S i.2 B 0 at hx; rw [show (0:Site c)=H 0 from (map_zero ..).symm,Orrery.low_home hC] at hx; obtain ⟨p,hp',rfl⟩:= mem_image.mp hx; rw [neighbors_mem,show (0:Site c)=H 0 from (map_zero ..).symm]; exact (Deck.less _ _ _).trans ((neighbors_mem ..).1 (hp hp'))
lemma high_downF (h : Margin B c) (i : Collection.Spikes C): ShortF B.B (J (peer hC i)) ↔ ShortF B.B (J i):= by
   rw [highEntry,highEntry,spread_short,spread_short]; constructor
   · intro hi; apply Orrery.walks hC B h S i.snd; intro x hx; apply (neighbors_mem ..).1; refine hi ?_; change _∈ (High.term S i.2).footprint 0; rw [show (0:Site c)= H 0 from (map_zero ..).symm, Deck.steadied hC]; exact mem_image_of_mem _ hx
   intro h x hx; change x∈ (High.term S i.2).footprint 0 at hx; rw [show (0:Site c)= H 0 from (map_zero ..).symm, Deck.steadied hC] at hx; obtain ⟨v,hv,rfl⟩:= mem_image.mp hx; apply (neighbors_mem ..).mpr; rw [show (0:Site c)= H 0 from (map_zero ..).symm]; exact (Deck.less _ _ _).trans ((neighbors_mem ..).1 (h hv))
-- Exhaustion. natural on used portions. one to *all* (post only guarded exactly on projection). Includes ALL analytic-based path atoms (not only short lengths).
omit hC
noncomputable def visiting (W:Curtain G c) (j:ℕ): Finset (Collection.EKey c) := Finset.filter (fun i=> ShortF B.B (Collection.incoming W.book S B i)) (Finset.disjSum W.sequence (Finset.disjSum (Finset.product (Finset.univ:Finset (Seat c)) ((Finset.range j).map (numbering Low).toEmbedding)) (Finset.product (Finset.univ:Finset (Seat c)) ((Finset.range j).map (numbering High).toEmbedding)))) -- assumes countable/infinite Low
variable {p:ℕ→ℕ}(L':Leaves hC p T.book.reg T.stamp.logRead V.book.reg V.stamp.logRead T.sequence V.sequence)
   (hv:Curtain.TidyC V B B.B ρ)(ht:Curtain.TidyC T B B.B ρ)(hw:Margin B c)(hG:G.Simple)
def casting (hC:C.val=c.val*k) (p:ℕ→ℕ) (i:Collection.EKey C): Collection.EKey c := Sum.map p (Sum.map (peer hC) (peer hC)) i
include hC L' hv ht hw hG
local notation "x"=> casting hC p -- name clash binder x later?
local notation "y"=> Collection.archive
local notation "Z"=> Averaging.delta (T.book.read T.stamp)
local notation "D"=> Averaging.delta (V.book.read V.stamp)
section walk
variable (n:ℕ)
omit hv ht L' hG in
private lemma low_iff (i:Collection.Faces C): Sum.inr (Sum.inl (peer hC i))∈ visiting B S V n ↔ Sum.inr (Sum.inl i)∈visiting B S T n:=by
   simp only [visiting,mem_filter,inr_mem_disjSum,inl_mem_disjSum, incoming,Sum.elim_inr,Sum.elim_inl,short_downF B S (hC:=hC) hw i]; constructor <;> (intro h; exact ⟨mem_product.mpr ⟨mem_univ _,(mem_product.mp h.1).2⟩,h.2⟩)
omit hv ht L' hG in
private lemma high_iff (i:Collection.Spikes C): Sum.inr (Sum.inr (peer hC i))∈ visiting B S V n ↔ Sum.inr (Sum.inr i)∈ visiting B S T n:= by
   simp only [visiting,mem_filter,inr_mem_disjSum,incoming,Sum.elim_inr,high_downF B S (hC:=hC) hw i]; constructor <;> (intro h; exact ⟨mem_product.mpr ⟨mem_univ _,(mem_product.mp h.1).2⟩,h.2⟩)
omit L' hv ht hw hC hG
lemma frame_iff (ht:Curtain.TidyC V B B.B ρ)(hb:2≤B.B)(i:ℕ) : Sum.inl i∈ visiting B S V n ↔ i∈ V.sequence:=by
   simp only [visiting,mem_filter,inl_mem_disjSum]; refine ⟨And.left,fun hi=>⟨hi,?_⟩⟩; rw [Orrery.short_iff]; intro a ha; obtain hx|hv:= mem_union.mp ha; exact (Orrery.short_iff _ _).mp (ht.frames i hi) hx; exact Corona.halo_mono hb (Finset.Subset.refl _) hv
include L' hv ht hw hC hG
set_option maxRecDepth 6000
set_option maxHeartbeats 550000 in
lemma stepping (hB:2 ≤ B.B)(t:Clip)(α:ℝ): Leaves hC (casting hC p) Q (y T.book S t T.stamp α Z) K (y V.book S t V.stamp α D) (visiting B S T n) (visiting B S V n):= by
    -- `notation x` - avoid binder
    have hf i:= frame_iff B S V n hv hB i; have hF i:= frame_iff B S T n ht hB i; have hx := tint hC V T B L' hv ht hw hG
    refine ⟨?_,?_,?_,?_,?_⟩
    · rintro (i|i|i) hi; · have he:= L'.root i ((hF i).1 hi); exact ⟨(hf _).2 he.1,he.2⟩
      · exact ⟨(low_iff B S V T (hC:=hC) hw n i).2 hi,rfl⟩ -- h args
      exact ⟨(high_iff B S V T (hC:=hC) hw n i).2 hi,rfl⟩
    · rintro (i|i|i) hi
      · have he:= (hF i).1 hi; change VerifiedReset.expand (V.book.reg (p i))= (VerifiedReset.expand (T.book.reg i)).image _
        unfold VerifiedReset.expand; rw [image_union, L'.stable i he,← (L'.root i he).2,← Finset.image_singleton H,Deck.ringed hC]
      · exact low_site B S (hC:=hC) i
      exact high_site S (hC:=hC) i
    · intro i hi U; rw [hx]; cases i with
      | inl i => exact Orrery.register hC B V T hw U L' ht hv hG i ((hF _).1 hi) -- arg order
      | inr i =>
         rcases i with i|i
         · change Low.fresh S t i.2 (0:Site C) _ (i.1.view ((F).links U)) = Low.fresh S t i.2 (0:Site c) _ _; rw [Meadow.estuary, Orrery.low_capture (hC:=hC),map_zero]; rfl
         change High.fresh S i.2 (0:Site C) _ _ (i.1.view ((F).links U))= High.fresh S i.2 (0:Site c) _ _ _; rw [Meadow.estuary,Orrery.high_capture (hC:=hC),map_zero]; rfl
    · rintro (i| ⟨⟨s,i⟩,j⟩|⟨⟨s,i⟩,j⟩) v hv' hq
      · obtain ⟨j,hj,hh,hK⟩:=L'.serves i v ((hf _).1 hv') hq; exact ⟨.inl j,(hF j).2 hj,congr_arg Sum.inl hh,hK⟩
      · let a:Collection.Faces C := ((s,v),j); rw [← (show H v=i from hq)] at hv'; exact ⟨.inr (.inl a),(low_iff B S V T (hC:=hC) hw n a |>.1 hv'),congr_arg (fun z=> (Sum.inr (Sum.inl ((s,z),j)))) hq,rfl⟩
      let a:Collection.Spikes C := ((s,v),j); rw [← (show H v=i from hq)] at hv'; exact ⟨.inr (.inr a),(high_iff B S V T (hC:=hC) hw n a |>.1 hv'),congr_arg (fun z=> (Sum.inr (Sum.inr ((s,z),j)))) hq,rfl⟩
    intro i j hi hj hu hk; unfold casting at hk; rcases i with i|i|i <;> rcases j with j|j|j <;> simp only [Sum.map_inl,Sum.map_inr, Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at hk ⊢ -- goals false
    all_goals first|exact False.elim hk|exact L'.uniqueness i j ((hF _).1 hi) ((hF _).1 hj) hu hk|exact peer_same i j hu.symm hk
end walk
end pricey
end YM.Juniper.Orrery
