import YM.RG01Estimate.Orison
/-!
 # Preserve all selected tuples across Deck. Heights independent of V values.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext.Repeat Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {Γ:Type} {c f C F L'' : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
lemma gardens {S:StepData c f}{T:Tube G S}{R: RG.Rep G f}{X : ConnectedActivityE6.Target G K} {p a W u:ℝ}
   {o: ConnectedActivityE6.Target.Order G W}(I:Cash W p a L'' X o u T R)(Q:Lex Γ f)(z:hall Γ c f) : arbor I Q z=z.biUnion (I.supportP ∘ mint S Q):= by
   unfold arbor Cash.unionP songs; ext i; constructor
   · intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj,rfl⟩:=mem_map.mp hk; exact mem_biUnion.mpr ⟨_,hj,hx⟩
   intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; exact mem_biUnion.mpr ⟨_,mem_map_of_mem _ hk,hx⟩
lemma patio {S:StepData c f}{T:Tube G S}{R: RG.Rep G f}{X : ConnectedActivityE6.Target G K} {p a W u:ℝ}
   {o: ConnectedActivityE6.Target.Order G W}(I:Cash W p a L'' X o u T R)(Q:Lex Γ f)(z:Sons Γ c f) (i:Option (Fin z.fst)) : arbor I Q (z.2 i)⊆arborX I Q z:= Finset.subset_biUnion_of_mem (arbor I Q ∘ z.2) (mem_univ _)

variable {h : f.val=c.val*P.L.val}{H:F.val=C.val*P.L.val}{Q: KernelChoices}{hC:C.val=c.val*M}{he:2≤c.val} {p u w W v:ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T:Tube G (stepped Q h)}{T':Tube G (stepped Q H)}{R:RG.Rep G f}{R':RG.Rep G F}{V:Lex Γ f}{V': Lex Γ F}
    {X:ConnectedActivityE6.Target G K}{o:ConnectedActivityE6.Target.Order G W}
variable (hp:R'.path=R.path) (I : Cash W p u L'' X o v T R) (I' : Cash W p u L'' X o w T' R') (A: Charts (h:=h) (H:=H) hC he R R' V V')
   (x:Site C) {d Z m : ℕ}

def follows (L' : Lace h H M) (s:Sons Γ C F): Sons Γ c f:= ⟨s.1,fun i=> (s.2 i).image (warps L')⟩
local notation "B" => radiusB p
local notation "P₀" => optic X.halo B d
local notation "W₀" => house X.halo B d m

include A I I' hp
lemma recession (i: Header Γ C F) : fit R'.path i=fit R.path (warps (L) i) ∧ I.supportP (mint (S) V (warps (L) i))=(I'.supportP (mint (Y) V' i)).image ((L).low.cut):= by
   have hc:= I.laws.data.room.buys; have hh: c.val ≤ f.val:= by rw [h]; exact Nat.le_mul_of_pos_right _ P.L.property; -- arithmetic
   exact sails (m:=X.halo) (b:=B) A hp (by omega) T T' i -- order
lemma crossing (p:hall Γ C F) : arbor I V (p.image (warps (L))) = (arbor I' V' p).image (L).low.cut:= by
   rw [gardens,gardens]; ext x; constructor
   · intro hx; obtain ⟨j,hj,hx⟩:= mem_biUnion.mp hx; obtain ⟨j,hj',rfl⟩:= mem_image.mp hj; dsimp only [Function.comp_apply] at hx; rw [(recession hp I I' A j).2] at hx; obtain ⟨i,hv,rfl⟩:= mem_image.mp hx; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨j,hj',hv⟩)
   intro h; obtain ⟨x,hx,rfl⟩:=mem_image.mp h; obtain ⟨z,hz,hv⟩:=mem_biUnion.mp hx; refine mem_biUnion.mpr ⟨_,mem_image_of_mem _ hz,?_⟩; dsimp only [Function.comp_apply]; rw [(recession hp I I' A z).2]; exact mem_image_of_mem _ hv
lemma cross (p:Sons Γ C F): arborX I V (follows (L) p)= (arborX I' V' p).image (L).low.cut:= by unfold arborX unionOf follows; ext i; simp only [Function.comp_apply, mem_image,mem_biUnion,crossing hp I I' A]; grind
lemma rolls (p:hall Γ C F)(hz:Set.InjOn (warps (Γ:=Γ) (L)) p)(hx:Set.InjOn (L).low.cut (arbor I' V' p)): Kind I' V' m p ↔ Kind I V m (p.image (warps (L))):= by
   have he' := Meadow.preheated (warps (L)) (I'.supportP ∘ mint (Y) V') (I.supportP ∘ mint (S) V) p (L).low.cut (fun i=> (recession hp I I' A i).2) hz (by rw [gardens] at hx; exact hx)
   have ht := card_image_of_injOn hz
   have hf {c f'} {W₁:StepData c f'} (p: Finset (Header Γ c f')) (V:Lex Γ f') (g: Head W₁→Support c): Ac.Spark g (songs V p) ↔Ac.Spark (g ∘ mint W₁ V) p:= by
      unfold songs; rw [Finset.map_eq_image]; exact (Meadow.sparkling _ _ p (Function.Embedding.injective _|>.injOn)).symm
   have ha : Ac.Spark I'.supportP (songs V' p)↔ Ac.Spark I.supportP (songs V (p.image (warps (L)))):= by
       apply Iff.trans (hf ..); apply Iff.trans _ (hf ..).symm; convert! he' using 2; congr; exact Subsingleton.elim _ _
   constructor
   · intro h; refine ⟨ha.1 h.active, ht.trans_lt h.size,fun i hi=>?_⟩; obtain ⟨i,hi',rfl⟩:=mem_image.mp hi; exact (recession hp I I' A i).1 ▸ h.vote i hi'
   intro h; refine ⟨ha.2 h.active,ht.symm.trans_lt h.size,fun i hi=> (recession hp I I' A i).1.trans_le (h.vote _ (mem_image_of_mem _ hi))⟩
variable (hV:StageMask R (stepped Q h) V d)(hW:StageMask R' (stepped Q H) V' d)
    (hZ: 2*house X.halo (radiusB p) d m<c.val)
include hW
omit A I hp
include hZ he in -- hC
lemma woven (s:Sons Γ C F) (Hq:Admit I' V' m s) (hc:x∈ arborX I' V' s) (i): Set.InjOn (warps (Γ:=Γ) (Lace.project (h:=h) (H:=H) hC he)) (↑(s.2 i) : Set (Header Γ C F)):= by
   intro y hy z hz ha; have hp:= (patio I' V' s i).trans (within I' V' m hW x Hq hc)
   exact (sailing (hC:=hC) (hc:=he) (h:=‹f.val=c.val*P.L.val›) (H:=H) Q).point hZ x y z ((neighbors_mem ..).1 (hp (positioned _ _ m _ (Hq.hot i) hW y hy))) ((neighbors_mem ..).1 (hp (positioned _ _ m _ (Hq.hot i) hW z hz))) ha

include A I hp
lemma parity {n:ℕ}(s:Sons Γ C F) (hS:∀ i, Kind I' V' m (s.2 i)) (hc:2*n<c.val) (ht:arborX I' V' s⊆ neighbors n x):
     coefficient (blocked (arbor I' V')) s.2 = coefficient (blocked (arbor I V)) (follows (L) s).2:= by
   have hf i: arbor I' V' (s.2 i)⊆neighbors n x:= (patio I' _ s i).trans ht
   apply Meadow.movement; intro i j; apply or_congr
   · constructor
     · exact fun he=> congr_arg (fun s:hall Γ C F=> s.image (warps (L))) he
     intro hP
     have he' := sailing (hC:=hC) (hc:=he) (h:=h) (H:=H) (Γ:=Γ) Q; let Z:=warps (Γ:=Γ) (L)
     have hg (i) (x': Header Γ C F)(h:x'∈ s.2 i): separation x (aisle _ x')≤ n:= (neighbors_mem ..).1 (hf i (positioned I' V' m (s.2 i) (hS i) hW x' h))
     have hx k j (he:(s.2 k).image Z=(s.2 j).image Z): s.2 k⊆ s.2 j:= by
         intro a ha; obtain ⟨b,hb,h⟩:= mem_image.mp (show Z a∈ (s.2 j).image Z from he ▸ (mem_image_of_mem Z ha))
         exact (he'.point hc x b a (hg _ _ hb) (hg _ _ ha) h) ▸ hb
     exact Finset.Subset.antisymm (hx _ _ hP) (hx _ _ hP.symm)
   unfold Ac.meets follows; dsimp only; rw [crossing hp I I' A,crossing hp I I' A]; constructor
   · rintro ⟨v,h,hx⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ hx⟩
   rintro ⟨v,h',hx⟩; obtain ⟨z,hv,hj⟩:=mem_image.mp h'; obtain ⟨y,hy,hr⟩:=mem_image.mp hx
   exact ⟨z,hv, ((Meadow.garden hC x hc) (hf _ hy) (hf _ hv) (hr.trans hj.symm)) ▸ hy⟩

include hZ
lemma orders (s:Sons Γ C F)(hs:Admit I' V' m s)(hx:x∈arborX I' V' s) : Admit I V m (follows (L) s) ∧ (L).low.cut x∈arborX I V (follows (L) s):= by
    have h':= within I' V' m hW x hs hx
    refine ⟨⟨hs.count, fun i=> ?_, (parity hp I I' A x hW s hs.hot hZ h') ▸ hs.glow⟩,?_⟩
    · exact (rolls hp I I' A (s.2 i) (woven (f:=f) I' x hW hZ s hs hx i) ((Meadow.garden hC x hZ).mono (coe_subset.mpr ((patio I' V' s i).trans h')))).1 (hs.hot i)
    rw [cross]; exact mem_image_of_mem _ hx; exact hp; exact A -- rw implicit
end YM.RG01Estimate.Evoc
