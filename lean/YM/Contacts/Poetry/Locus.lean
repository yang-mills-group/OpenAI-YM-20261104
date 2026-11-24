import YM.Contacts.Poetry.Hangar
import YM.Contacts.Poetry.Fair
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Span
/-! Adapted from Meadow/{Vista,Span,Tuft}. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Poetry
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {n₀ m₀ m:ℕ}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he)
    {Ξ:Lecturer R m₀}{Ξ':Lecturer R' m₀}
-- includes length/ground but not val bills
local notation "B" => radiusB p
lemma footland (p:Park C F) : Poetry.ground I' Ξ' p=p.biUnion (I'.supportP ∘ topic (Y) Ξ'):= by
  unfold Poetry.ground Cash.unionP Poetry.caste
  ext i; constructor
  · intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj,rfl⟩:=mem_map.mp hk; exact mem_biUnion.mpr ⟨_,hj,hx⟩
  intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; exact mem_biUnion.mpr ⟨_,mem_map_of_mem _ hk,hx⟩
section vegas
variable (hp : R'.path= R.path)
include hC he hp I I'
lemma contempt (i:Meter C F) : vote R'.path i=vote R.path (aisle (L) i) ∧ I.supportP (topic (S) Ξ (aisle (L) i))=(I'.supportP (topic (Y) Ξ' i)).image ((L).low.cut):= by
  have hc:= I.laws.data.room.buys; have hh: c.val ≤ f.val:= by rw [h]; exact Nat.le_mul_of_pos_right _ P.L.property
  exact Poetry.parallel Ξ Ξ' (he:=he) (hC:=hC) (T:=T) (T':=T') i X.halo (B) hp (by omega)
lemma pitched (i:Park C F): Poetry.ground I Ξ (wrappersP (L) i)= (Poetry.ground I' Ξ' i).image (L).low.cut:= by
  have heq j : I.supportP (topic (S) Ξ (aisle (L) j))=_:= (contempt (Ξ:=Ξ) (Ξ':=Ξ') (I:=I) (I':=I') hC he hp j).2
  rw [footland,footland]; unfold wrappersP; ext x; constructor
  · intro h; obtain ⟨j,hj,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj',rfl⟩:= mem_image.mp hj; dsimp only [Function.comp_apply] at hx; rw [heq] at hx; obtain ⟨i,hv,rfl⟩:= mem_image.mp hx; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨j,hj',hv⟩)
  intro h; obtain ⟨x,hx,rfl⟩:=mem_image.mp h; obtain ⟨z,hz,hv⟩:=mem_biUnion.mp hx; refine mem_biUnion.mpr ⟨_,mem_image_of_mem _ hz,?_⟩; dsimp only [Function.comp_apply]; rw [heq]; exact mem_image_of_mem _ hv
lemma seed_order (p:Park C F) (heq:Set.InjOn (aisle (L)) p) (hh:Set.InjOn ((L).low.cut) (Poetry.ground I' Ξ' p)) : Seed I' Ξ' n₀ p ↔ Seed I Ξ n₀ (wrappersP (L) p):= by
  have he' := Meadow.preheated (aisle (L)) (I'.supportP ∘ topic (Y) Ξ') (I.supportP ∘ topic (S) Ξ) p (L).low.cut (fun i=> (contempt (Ξ:=Ξ) (Ξ':=Ξ') hC he (I:=I) (I':=I') hp i).2) heq (by rw [footland] at hh; exact hh)
  have ht := card_image_of_injOn heq
  have hf {c f'} {W₁:StepData c f'} {W₂:RG.Rep G f'} (U:Lecturer W₂ m₀) (p: Finset (Meter c f')) (g: Head W₁→Support c): Ac.Spark g (caste U W₁ p) ↔Ac.Spark (g ∘ topic W₁ U) p:= by
    unfold Poetry.caste; rw [Finset.map_eq_image]; exact (Meadow.sparkling _ _ p (Function.Embedding.injective _|>.injOn)).symm
  have ha : Ac.Spark I'.supportP (caste Ξ' _ p) ↔Ac.Spark I.supportP (caste Ξ _ (wrappersP (L) p)):= (hf Ξ' p _).trans ((show Ac.Spark (I'.supportP ∘ topic (Y) Ξ') p ↔ Ac.Spark (I.supportP ∘ topic (S) Ξ) (wrappersP (L) p) from (by convert! he' using 2; unfold wrappersP; congr; exact Subsingleton.elim _ _)).trans (hf Ξ (wrappersP (L) p) I.supportP).symm)
  constructor
  · intro h; refine ⟨ha.1 h.hot,ht ▸ h.sizes,fun i hi=>?_⟩; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; exact (contempt (Ξ:=Ξ) (Ξ':=Ξ') hC he hp (I:=I) (I':=I') i).1 ▸ h.earns _ (by assumption)
  intro h; refine ⟨ha.2 h.hot,ht ▸ h.sizes,fun i hi=> (contempt (Ξ:=Ξ) (Ξ':=Ξ') hC he hp (I:=I) (I':=I') i).1.trans_le (h.earns _ (mem_image_of_mem _ hi))⟩

end vegas
local notation "D" => roomP X.halo B m₀ n₀
local notation "t" => generous X.halo B m₀
variable (x : Site C)
def forward (V:Lace h H M) (p:Vines C F) : Vines c f:= ⟨p.fst, wrappersP V ∘ p.snd⟩
include hC
lemma garden (he : 2*D'<c.val) : Set.InjOn (Macrame.splitter (Deck.divides hC)) (neighbors D' x):= by
  intro i hi j hj h; apply tiniest _ h; apply (separation_triangle _ x _).trans_lt; rw [separation_comm i]; have h₁ := (neighbors_mem ..).1 (Finset.mem_coe.mp hi); have h₂:= (neighbors_mem ..).1 (Finset.mem_coe.mp hj); omega
include he
lemma genitive (hh : 2*D'<c.val) {v w: Park C F} (hz:∀ i∈v,separation x (lobby (Y) i)≤D') (ht:∀ i∈w,separation x (lobby (Y) i)≤D') (hp:wrappersP (L) v=wrappersP (L) w) : v=w:= by
  let L':=aisle (L); have he:=senate (hC:=hC) (he:=he) (h:=h) (H:=H) (Q:=Q); ext i; constructor
  · intro hi; obtain ⟨j,hj,hp⟩:= mem_image.mp (show L' i∈ wrappersP (L) w from hp ▸ (show L' i ∈ wrappersP (L) v from mem_image_of_mem L' hi)); exact (he.point hh x i j (hz i hi) (ht j hj) hp.symm).symm ▸ hj
  intro hi; obtain ⟨j,hj,hp⟩:=mem_image.mp (show L' i∈wrappersP (L) v from hp.symm ▸ (show L' i∈wrappersP (L) w from mem_image_of_mem L' hi)); exact (he.point hh x i j (ht i hi) (hz j hj) hp.symm).symm ▸ hj
omit hC he in
lemma engirds (v:Vines C F) (hv:Stir I' Ξ' n₀ v) (hz:x∈Poetry.stampP I' Ξ' v) (i): Poetry.ground I' Ξ' (v.2 i)⊆neighbors D x:= (your (H:=I') (z:=v) i).trans (entered hv x hz)
lemma inquire (v u: Vines C F) (hv:Stir I' Ξ' n₀ v) (hu:Stir I' Ξ' n₀ u) (hx:x∈Poetry.stampP I' Ξ' v) (hk:x∈Poetry.stampP I' Ξ' u) (hC':2 * D < c.val) (h:forward (L) u=forward (L) v): u=v:= by
  have he : u.fst=v.fst:= congr_arg (fun i : Vines c f=> i.fst) h; rcases v with ⟨n,v⟩; rcases u with ⟨m,u⟩; dsimp only at he; subst m
  unfold forward at h; injection h with h hh; congr 1; funext i; let V:=v
  apply genitive (Q:=Q) hC (by assumption) x hC' _ _ (congr_fun hh i)
  · intro j hk'; exact (neighbors_mem ..).1 ((your (H:=I') (z:=⟨_,u⟩) i|>.trans (entered hu x hk)) (centers (hu.each i) hk'))
  intro j hk; exact (neighbors_mem ..).1 ((your (H:=I') (z:=⟨_,v⟩) i|>.trans (entered hv x hx)) (centers (hv.each i) hk))
lemma rings (v:Vines C F) (hv:Stir I' Ξ' n₀ v) (hx:x∈ Poetry.stampP I' Ξ' v) (hp:2*D<c.val) (i) : Set.InjOn (aisle (L)) (↑(v.2 i) : Set (Meter C F)):= by
  have hI:= engirds x v hv hx i
  intro y hy z hz he; exact (senate (Q:=Q) (hC:=hC) (he:=by assumption) (h:=h) (H:=H)).point hp x y z ((neighbors_mem ..).1 (hI (centers (hv.each i) hy))) ((neighbors_mem ..).1 ((your (H:=I') (z:=v) i).trans (entered hv x hx) (centers (hv.each i) hz))) he
variable (hp : R'.path=R.path)
include hp I I'
lemma pitchRoll (z: Vines C F) : Poetry.stampP I Ξ (forward (L) z)= (Poetry.stampP I' Ξ' z).image (L).low.cut:= by unfold stampP forward; unfold unionOf; ext i; simp only [Function.comp_apply, mem_image,mem_biUnion,pitched (Ξ:=Ξ) (Ξ':=Ξ') (I:=I) (I':=I') hC he hp]; grind
lemma receipts (z:Vines C F) (hZ:2*D'< c.val) (hz: Poetry.stampP I' Ξ' z⊆ neighbors D' x) (hu: ∀ i,Seed I' Ξ' n₀ (z.2 i)) :
    coefficient (blocked (Poetry.ground I' Ξ')) z.2=coefficient (blocked (Poetry.ground I Ξ)) (forward (L) z).2:= by
  apply Meadow.movement; intro i j; let f:=Poetry.ground I' Ξ'; have hf i: f (z.2 i)⊆neighbors D' x := (your (H:=I') (z:=z) _).trans hz
  have hm i s (hh:s∈z.2 i):separation x (lobby Y s) ≤ D':= (neighbors_mem ..).1 (hf i (centers (hu i) hh)); have hv i: ((Poetry.ground I Ξ ∘ (forward (L) z).2) i)=(f (z.2 i)).image (L).low.cut:= pitched (Ξ:=Ξ) (Ξ':=Ξ') hC he hp _
  have hy i : Poetry.ground I Ξ ((forward (L) z).2 i)= (f (z.2 i)).image (L).low.cut:= hv i
  apply or_congr; · exact ⟨fun hx=>congr_arg (wrappersP (L)) hx,genitive hC he x hZ (hm i) (hm j)⟩
  unfold Ac.meets; rw [hy,hy]; constructor
  · rintro ⟨v,h,hx⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ hx⟩
  rintro ⟨v,h',hx⟩; obtain ⟨z,hv,hj⟩:=mem_image.mp h'; obtain ⟨y,hy,hr⟩:=mem_image.mp hx
  -- compare labels via hZ; priority
  exact ⟨z,hv, ((garden hC x hZ) (hf _ hy) (hf _ hv) (hr.trans hj.symm)) ▸ hy⟩
lemma stitches (z:Vines C F) (hv:Stir I' Ξ' n₀ z) (hk:x∈Poetry.stampP I' Ξ' z) (hH:2 * D< c.val) : Stir I Ξ n₀ (forward (L) z) ∧ (L).low.cut x∈Poetry.stampP I Ξ (forward (L) z):= by
  have hS:= entered hv x hk
  refine ⟨⟨hv.small,fun i=> ?_,((receipts (Ξ:=Ξ) (Ξ':=Ξ') (I':=I') hC he x (I:=I) hp z hH hS hv.each) ▸ hv.moves)⟩,?_⟩
  · apply (seed_order (Ξ:=Ξ) (Ξ':=Ξ') (I:=I) (I':=I') hC he hp _ (rings hC he x z hv hk hH i) ((garden hC x hH).mono _)).1 (hv.each i)
    exact coe_subset.mpr ((your (z:=z) i).trans hS)
  rw [pitchRoll (Ξ:=Ξ) (Ξ':=Ξ') (I:=I) (I':=I') hC he hp z]; exact mem_image_of_mem _ hk
local notation "τ" => generous X.halo B m₀
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
lemma ramify (z: Park c f) (h: Seed I Ξ n₀ z) (hk : Poetry.ground I Ξ z⊆ neighbors D' x') (ht : D'+τ≤ m) (hm: 2 * m < c.val) : ∃ v, Seed I' Ξ' n₀ v ∧ Poetry.ground I' Ξ' v⊆neighbors m x ∧ wrappersP (L) v=z := by
  let P:= L 
  let y := aisle P
  choose Y' HY hp' using (senate (h:=by assumption) (H:=H) (Q:=Q) (hC:=hC) (he:=he)).esc x -- maybe inference
  let v:=z.image Y'
  have hx' i (hi:i∈z) : separation x (lobby Y (Y' i)) ≤ D':=(hp' i).trans_le ((neighbors_mem ..).1 (hk (centers h hi)))
  have hr k (hk:k∈v): lobby Y k ∈ Poetry.ground I' Ξ' v ∧ I'.supportP (topic (Y) Ξ' k) ⊆ neighbors m x:= by
    obtain ⟨p,hpK,rfl⟩:= mem_image.mp hk; let A':=Y' p; have hh:= contempt (Ξ:=Ξ) (Ξ':=Ξ') hC he hp (I:=I) (I':=I') A'; have ht' := hx' p hpK
    obtain ⟨hz,hV⟩:= Poetry.domain Ξ' X.halo B (lt_of_lt_of_le (by norm_num) I'.laws.data.room.sight.1) T' A' (((hh.1.trans (congr_arg (vote R.path) (HY p))).trans_le (h.earns _ hpK)))
    refine ⟨mem_biUnion.mpr ⟨_,mem_map_of_mem (topic Y Ξ') (show A'∈ v from mem_image_of_mem _ hpK),hz⟩, fun i hi=> ?_⟩; apply (neighbors_mem ..).2; exact (separation_triangle _ (lobby Y A') _).trans ((Nat.add_le_add ht' ((neighbors_mem ..).1 (hV hi))).trans ht)
  have hM:Poetry.ground I' Ξ' v⊆neighbors m x:= by intro i hi; obtain ⟨k,hk,h⟩:= mem_biUnion.mp hi; obtain ⟨s,hs,rfl⟩:=mem_map.mp hk; exact (hr s hs).2 h
  have ht': Set.InjOn (aisle P) v:= fun i hi j hj hh=> (senate (hC:=hC) (he:=he) (h:=by assumption) (H:=H) (Q:=Q)).point hm x i j ((neighbors_mem ..).1 (hM (hr i hi).1)) ((neighbors_mem ..).1 (hM (hr j hj).1)) hh
  have hL:wrappersP P v=z:= by unfold wrappersP v; rw [Finset.image_image,show aisle P ∘ Y'=id from funext HY,image_id]
  exact ⟨v,(seed_order (Ξ:=Ξ) (Ξ':=Ξ') hC he hp v (I:=I) (I':=I') ht' ((garden hC x hm).mono (coe_subset.mpr hM))).2 (hL.symm ▸ h),hM,hL⟩
lemma returns (s: Vines c f) (hs: Stir I Ξ n₀ s) (hx:x'∈Poetry.stampP I Ξ s) (hH:2*(D+τ) < c.val):
    ∃ u, Stir I' Ξ' n₀ u∧ x∈Poetry.stampP I' Ξ' u∧ forward (L) u=s:= by
  choose f hp' hZ hf using fun i=> ramify (Ξ:=Ξ) (Ξ':=Ξ') hC he x hp (I:=I) (I':=I') (s.2 i) (hs.each i) ((your (z:=s) i).trans (entered hs x' hx)) le_rfl hH
  let u:Vines C F:= ⟨s.1,f⟩
  have h : forward (L) u=s:= by unfold forward u; congr 1; exact funext hf
  have ht : Poetry.stampP I' Ξ' u⊆ neighbors (D+τ) x:= by
    intro i hi; obtain ⟨j,-,hq⟩:=mem_biUnion.mp hi; exact hZ j hq
  have hy := receipts (Ξ:=Ξ) (Ξ':=Ξ') (I:=I) hC he x hp u hH ht hp'; rw [h] at hy
  refine ⟨u,⟨hs.small,hp',hy.symm ▸ hs.moves⟩,?_,h⟩
  obtain ⟨i,hk,hh⟩:=mem_image.mp (show (L).low.cut x∈ (Poetry.stampP I' Ξ' u).image (L).low.cut from (by rw [← pitchRoll (Ξ:=Ξ) (Ξ':=Ξ') hC he hp (I:=I) (I':=I') u,h]; exact hx))
  exact ((garden hC x hH (ht hk) (show x ∈ neighbors _ x from (neighbors_mem ..).2 (by simp)) hh) : i=x) ▸ hk
end YM.PhysicalNext.Repeat.Poetry
