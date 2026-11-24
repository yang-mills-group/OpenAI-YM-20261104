import YM.AllOrder.Burn.Quad
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Tuft

/-! # Genuine replication on Ink. Not assuming periods equal/dense. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo Meadow
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M k j m π u d: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
local notation "B" => radiusB p
local notation "τ" => Mint.width X.halo (radiusB p) (2*radiusB p)
open Meadow (Park)
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (x:Site C) (hp:R'.path=R.path)
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
variable {φ:Locale G} (s₁:Burn.Seed R' φ)(s₀:Burn.Seed R φ)(hq:R'.p=R.p)(hQ:R.p.B≤2*radiusB p)
include hC he
lemma vias : Deck.Nest (Deck.divides hC) (plode (L)) (stepsV (Y)) (stepsV (S)) := (Stellar.nest_mint (Q:=Q) (hC:=hC) (he:=he)).sum (Deck.footing ..)
omit hC he in
lemma footlandT (p:Yard C F) : thing I' s₁ p=p.biUnion (I'.supportP ∘ spin (Y) s₁.model):= by
  unfold thing Cash.unionP stages
  ext i; constructor
  · intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj,rfl⟩:=mem_map.mp hk; exact mem_biUnion.mpr ⟨_,hj,hx⟩
  intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; exact mem_biUnion.mpr ⟨_,mem_map_of_mem _ hk,hx⟩
lemma genitiveT (hh : 2*d<c.val) {v w: Yard C F} (hz:∀ i∈v,separation x (stepsV (Y) i)≤d) (ht:∀ i∈w,separation x (stepsV (Y) i)≤d) (hp:wrapper (L) v=wrapper (L) w) : v=w:= by
  let L':=plode (L); have he:=vias (hC:=hC) (he:=he) (h:=h) (H:=H) (Q:=Q); ext i; constructor
  · intro hi; obtain ⟨j,hj,hp⟩:= mem_image.mp (show L' i∈ wrapper (L) w from hp ▸ (show L' i ∈ wrapper (L) v from mem_image_of_mem L' hi)); exact (he.point hh x i j (hz i hi) (ht j hj) hp.symm).symm ▸ hj
  intro hi; obtain ⟨j,hj,hp⟩:=mem_image.mp (show L' i∈wrapper (L) v from hp.symm ▸ (show L' i∈wrapper (L) w from mem_image_of_mem L' hi)); exact (he.point hh x i j (ht i hi) (hz j hj) hp.symm).symm ▸ hj
include hp hq I I'
lemma contemptT (i:Mandala C F) : ageV R'.path i=ageV R.path (plode (L) i) ∧ I.supportP (spin (S) s₀.model (plode (L) i))=(I'.supportP (spin (Y) s₁.model i)).image ((L).low.cut):= by
  have hc:= I.laws.data.room.buys; have hh: c.val ≤ f.val:= by rw [h]; exact Nat.le_mul_of_pos_right _ P.L.property
  rcases i with i|i
  · exact Stellar.voy (he:=he) (hC:=hC) (T:=T) (T':=T') i X.halo (B) hp (by omega)
  exact ⟨rfl,reg_scape hC he φ s₀ s₁ hq X.halo B i (by omega)⟩
lemma pitchedT (i:Yard C F): thing I s₀ (wrapper (L) i)= (thing I' s₁ i).image (L).low.cut:= by
  have heq j : I.supportP (spin (S) s₀.model (plode (L) j))=_:= (contemptT (I:=I) (I':=I') hC he hp s₁ s₀ hq j).2
  rw [footlandT,footlandT]; unfold wrapper; ext x; constructor
  · intro h; obtain ⟨j,hj,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj',rfl⟩:= mem_image.mp hj; dsimp only [Function.comp_apply] at hx; rw [heq] at hx; obtain ⟨i,hv,rfl⟩:= mem_image.mp hx; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨j,hj',hv⟩)
  intro h; obtain ⟨x,hx,rfl⟩:=mem_image.mp h; obtain ⟨z,hz,hv⟩:=mem_biUnion.mp hx; refine mem_biUnion.mpr ⟨_,mem_image_of_mem _ hz,?_⟩; dsimp only [Function.comp_apply]; rw [heq]; exact mem_image_of_mem _ hv
lemma crew_port (p:Yard C F) (heq:Set.InjOn (plode (L)) p) (hh:Set.InjOn ((L).low.cut) (thing I' s₁ p)) : Crew I' s₁ π k p ↔ Crew I s₀ π k (wrapper (L) p):= by
  -- from Meadow.seed_order
  have he' := preheated (plode (L)) (I'.supportP ∘ spin (Y) s₁.model) (I.supportP ∘ spin (S) s₀.model) p (L).low.cut (fun i=> (contemptT hC he hp s₁ s₀ hq (I:=I) (I':=I') i).2) heq (by rw [footlandT] at hh; exact hh)
  have ht := card_image_of_injOn heq
  have hf {c f'} {W₁:StepData c f'} (model:Site f'↪ℕ) (p: Finset (Mandala c f')) (g: Head W₁→Support c): Ac.Spark g (stages W₁ model p) ↔Ac.Spark (g ∘ spin W₁ model) p:= by
    unfold stages; rw [Finset.map_eq_image]; exact (sparkling _ _ p (Function.Embedding.injective _|>.injOn)).symm
  have ha : Ac.Spark I'.supportP (stages (Y) s₁.model p) ↔Ac.Spark I.supportP (stages (S) s₀.model (wrapper (L) p)):= (hf _ p _).trans ((show Ac.Spark (I'.supportP ∘ spin (Y) s₁.model) p ↔ Ac.Spark (I.supportP ∘ spin (S) s₀.model) (wrapper (L) p) from (by convert! he' using 2; unfold wrapper; congr; exact Subsingleton.elim _ _)).trans (hf _ (wrapper (L) p) I.supportP).symm)
  have hk i : i∈clan (c:=C) (f:=F) k ↔ (plode (L) i)∈ clan k:= by
    rcases i with i|i; · unfold clan; simp only [plode,Sum.map_inl,inl_mem_disjSum,Meadow.pocket]; rcases i with i|i|i|i <;> rfl
    simp [clan,plode]
  constructor
  · intro h; refine ⟨(hq ▸ h.radius),ha.1 h.hot,ht ▸ h.sizes,fun i hi=>?_, fun i hi=> ?_⟩
    · obtain ⟨i,hi',rfl⟩:=mem_image.mp hi; exact (contemptT hC he hp s₁ s₀ hq (I:=I) (I':=I') i).1 ▸ h.earns _ hi'
    obtain ⟨i,hi',rfl⟩:=mem_image.mp hi; exact (hk i).1 (h.slots hi')
  intro h; refine ⟨(hq ▸ h.radius),ha.2 h.hot,ht ▸ h.sizes,fun i hi=> (contemptT hC he hp s₁ s₀ hq (I:=I) (I':=I') i).1.trans_le (h.earns _ (mem_image_of_mem _ hi)), fun i hi=> ?_⟩
  exact (hk i).2 (h.slots (mem_image_of_mem _ hi))

omit hp hq I in
lemma agency (ht:2*d < c.val) {z:Yard C F} (h : Crew I' s₁ π k z) (hv : thing I' s₁ z⊆ neighbors d x): Set.InjOn (plode (L)) z:= by
  intro i hi j hj hh
  exact (vias (Q:=Q) (hC:=hC) (he:=he) (h:=by assumption) (H:=H)).point ht x i j ((neighbors_mem ..).1 (hv (center_ticket h i hi))) ((neighbors_mem ..).1 (hv (center_ticket h j hj))) hh

lemma meets_home (z: Yard c f) (h: Crew I s₀ π k z) (hk : thing I s₀ z ⊆ neighbors d x') (ht : d+τ≤ m) (hm: 2*m<c.val) : ∃ v, Crew I' s₁ π k v ∧ thing I' s₁ v⊆neighbors m x ∧ wrapper (L) v=z := by
  -- version of ramify with tickets carried
  let P:= L
  choose Y' HY hp' using (vias (h:=by assumption) (H:=H) (Q:=Q) (hC:=hC) (he:=he)).esc x
  let v:=z.image Y'; have hx' i (hi:i∈z) : separation x (stepsV Y (Y' i)) ≤ d:=(hp' i).trans_le ((neighbors_mem ..).1 (hk (center_ticket h i hi)))
  have hr k (hk:k∈v): stepsV Y k ∈ thing I' s₁ v ∧ I'.supportP (spin (Y) s₁.model k) ⊆ neighbors m x:= by
    obtain ⟨p,hpK,rfl⟩:= mem_image.mp hk; let A':=Y' p; have hh:= contemptT hC he hp s₁ s₀ hq (I:=I) (I':=I') A'; have ht' := hx' p hpK
    obtain ⟨hz,hV⟩:= Burn.footing (H:=I') s₁ (hq ▸ h.radius) A' (((hh.1.trans (congr_arg (ageV R.path) (HY p))).trans_le (h.earns _ hpK)))
    refine ⟨mem_biUnion.mpr ⟨_,mem_map_of_mem (spin (Y) s₁.model) (show A'∈ v from mem_image_of_mem _ hpK),hz⟩, fun i hi=> ?_⟩; apply (neighbors_mem ..).2; exact (separation_triangle _ (stepsV Y A') _).trans ((Nat.add_le_add ht' ((neighbors_mem ..).1 (hV hi))).trans ht)
  have hM:thing I' s₁ v⊆neighbors m x:= by intro i hi; obtain ⟨k,hk,h⟩:= mem_biUnion.mp hi; obtain ⟨s,hs,rfl⟩:=mem_map.mp hk; exact (hr s hs).2 h
  have ht': Set.InjOn (plode P) v:= fun i hi j hj hh=> (vias (hC:=hC) (he:=he) (h:=by assumption) (H:=H) (Q:=Q)).point hm x i j ((neighbors_mem ..).1 (hM (hr i hi).1)) ((neighbors_mem ..).1 (hM (hr j hj).1)) hh
  have hL:wrapper P v=z:= by unfold wrapper v; rw [Finset.image_image,show plode P ∘ Y'=id from funext HY,image_id]
  exact ⟨v,(crew_port hC he hp s₁ s₀ hq (I:=I) (I':=I') v ht' ((garden hC x hm).mono (coe_subset.mpr hM))).2 (hL.symm ▸ h),hM,hL⟩

variable (ht:T'=Deck.re T) (hζ:R'.beta=R.beta) (χ:Chi) (A:Config G c) (ha:RG.flags (Pressure.temp p) A=∅)
local notation "Z" => splitter (Deck.divides hC)
include ht hζ ha χ
lemma rendition (π k : ℕ) (hr: d+τ ≤ m) (hm:4*m < c.val) : Nonempty (High.ExchangeP (Z) (steady I s₀ π k) (steady I' s₁ π k) χ x ((L).low.links A) A d m) := by
  let Γ (i:I'.ThinP) (j:I.ThinP) := ∃ z:Yard C F,Crew I' s₁ π k z ∧ I'.smallAt i ⊆ neighbors m x∧ i.val=stages Y s₁.model z ∧ j.val=stages S s₀.model (wrapper (L) z)
  have heq:2*m<c.val:=by omega
  have hx:= garden hC x heq; have hΩ {z} (hb : Crew I' s₁ π k z) (hv: thing I' s₁ z⊆ neighbors m x):= crew_port (π:=π) (k:=k) hC he (I:=I) hp s₁ s₀ hq z (agency hC he x s₁ heq hb hv) ((garden hC x heq).mono (Finset.coe_subset.mpr hv))
  refine ⟨⟨Γ,fun i hi hy=> ?_,fun j hj hz=> ?_,?_,?_,?_,?_⟩⟩
  · obtain ⟨z,h,r⟩:= steady_mem.1 hi; obtain rfl : i=activeM h:= Subtype.ext r
    have hy' : thing I' s₁ z⊆neighbors m x:= hy.trans (fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega)))
    have hv:= (hΩ h hy').1 h; exact ⟨activeM hv,steady_mem.2 ⟨_,hv,rfl⟩,_,h,hy',rfl,rfl⟩
  · obtain ⟨z,h,r⟩:= steady_mem.1 hj; obtain rfl : j=activeM h := Subtype.ext r
    obtain ⟨v,hv,hV,hz⟩:= meets_home (I':=I') hC he x hp s₁ s₀ hq z h hz hr heq
    exact ⟨activeM hv,steady_mem.2 ⟨_,hv,rfl⟩, hV, v,hv,hV,rfl, (congr_arg (stages S s₀.model) hz).symm⟩
  · rintro i j k ⟨z,hz,hZ,h,r⟩ ⟨v,hv,hv',g,h'⟩; have he:z=v:=Finset.map_injective (spin (Y) s₁.model) (h.symm.trans g); rw [he] at r; exact Subtype.ext (r.trans h'.symm)
  · rintro i j k hx hy ⟨z,hz,hZ,h,r⟩ ⟨v,hv,hV,g,h'⟩; have hett : i=activeM hz:=Subtype.ext h; rw [hett] at hZ; have hs b (hh:b∈z):separation x (stepsV Y b) ≤ m:= (neighbors_mem ..).1 (hZ (center_ticket hz b hh))
    have hu : k=activeM hv:=Subtype.ext g; rw [hu] at hV
    have ht := genitiveT hC he x heq hs (fun i hi=> (neighbors_mem ..).1 (hV (center_ticket hv i hi))) (Finset.map_injective (spin (S) s₀.model) (r.symm.trans h'))
    exact Subtype.ext (h.trans ((congr_arg _ ht).trans g.symm))
  · rintro i j ⟨z,hz,hQ,h,hp'⟩; rw [show i=activeM hz from Subtype.ext h] at *; change I.unionP j.val= _; rw [hp']; exact pitchedT hC he hp s₁ s₀ hq (I:=I) (I':=I') z
  rintro i j ⟨z,hz,hQ,h,hp'⟩; obtain rfl : i=activeM hz:= Subtype.ext h; change _ = I.spawn _ _ j.val; rw [hp']; have hk:thing I' s₁ z⊆_:=(show I'.smallAt (activeM hz)⊆ neighbors m x from hQ); exact meetupsT hC he φ s₁ s₀ (hq ▸ hz.radius) I' I ht hp hq hζ x m (by omega) (agency hC he x s₁ heq hz hk) hk hz.earns A χ ha hz.hot ((hΩ hz hk).1 hz).hot
end YM.AllOrder.Burn
