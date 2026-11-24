import YM.AllOrder.High.Cursor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Tuft

/-! # Genuine replication on Ink. Not assuming periods equal/dense. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo Meadow
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M k j m π u d: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
local notation "B" => radiusB p
local notation "τ" => Mint.width X.halo (radiusB p) (radiusB p)
open Meadow (Park)
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (x:Site C) (hp:R'.path=R.path)
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
include hC he hp I I'
lemma crew_port (p:Park C F) (heq:Set.InjOn (verse_down (L)) p) (hh:Set.InjOn ((L).low.cut) (Meadow.ground I' p)) : Crew I' π k p ↔ Crew I π k (wrappers (L) p):= by
  -- from Meadow.seed_order
  have he' := preheated (verse_down (L)) (I'.supportP ∘ disc (Y)) (I.supportP ∘ disc (S)) p (L).low.cut (fun i=> (contempt hC he hp (I:=I) (I':=I') i).2) heq (by rw [footland] at hh; exact hh)
  have ht := card_image_of_injOn heq
  have hf {c f'} {W₁:StepData c f'} (p: Finset (Music c f')) (g: Head W₁→Support c): Ac.Spark g (hatch W₁ p) ↔Ac.Spark (g ∘ disc W₁) p:= by
    unfold hatch; rw [Finset.map_eq_image]; exact (sparkling _ _ p (Function.Embedding.injective _|>.injOn)).symm
  have ha : Ac.Spark I'.supportP (hatch _ p) ↔Ac.Spark I.supportP (hatch _ (wrappers (L) p)):= (hf p _).trans ((show Ac.Spark (I'.supportP ∘ disc (Y)) p ↔ Ac.Spark (I.supportP ∘ disc (S)) (wrappers (L) p) from (by convert! he' using 2; unfold wrappers; congr; exact Subsingleton.elim _ _)).trans (hf (wrappers (L) p) I.supportP).symm)
  have hk i : i∈Meadow.tuck (c:=C) (f:=F) k ↔ (verse_down (L) i)∈ Meadow.tuck k:= by rw [Meadow.pocket,Meadow.pocket]; rcases i with i|i|i|i <;> rfl
  constructor
  · intro h; refine ⟨ha.1 h.hot,ht ▸ h.sizes,fun i hi=>?_, fun i hi=> ?_⟩
    · obtain ⟨i,hi',rfl⟩:=mem_image.mp hi; exact (contempt hC he hp (I:=I) (I':=I') i).1 ▸ h.earns _ hi'
    obtain ⟨i,hi',rfl⟩:=mem_image.mp hi; exact (hk i).1 (h.slots hi')
  intro h; refine ⟨ha.2 h.hot,ht ▸ h.sizes,fun i hi=> (contempt hC he hp (I:=I) (I':=I') i).1.trans_le (h.earns _ (mem_image_of_mem _ hi)), fun i hi=> ?_⟩
  exact (hk i).2 (h.slots (mem_image_of_mem _ hi))

omit hp I in
lemma agency (ht:2*d < c.val) {z:Park C F} (h : Crew I' π k z) (hv : Meadow.ground I' z⊆ neighbors d x): Set.InjOn (verse_down (L)) z:= by
  intro i hi j hj hh
  exact (nest_mint (Q:=Q) (hC:=hC) (he:=he) (h:=by assumption) (H:=H)).point ht x i j ((neighbors_mem ..).1 (hv (center_ticket h i hi))) ((neighbors_mem ..).1 (hv (center_ticket h j hj))) hh

lemma meets_home (z: Park c f) (h: Crew I π k z) (hk : Meadow.ground I z ⊆ neighbors d x') (ht : d+τ≤ m) (hm: 2*m<c.val) : ∃ v, Crew I' π k v ∧ Meadow.ground I' v⊆neighbors m x ∧ wrappers (L) v=z := by
  -- version of ramify with tickets carried
  let P:= L
  choose Y' HY hp' using (nest_mint (h:=by assumption) (H:=H) (Q:=Q) (hC:=hC) (he:=he)).esc x
  let v:=z.image Y'; have hx' i (hi:i∈z) : separation x (pace Y (Y' i)) ≤ d:=(hp' i).trans_le ((neighbors_mem ..).1 (hk (center_ticket h i hi)))
  have hr k (hk:k∈v): pace Y k ∈ Meadow.ground I' v ∧ I'.supportP (disc (Y) k) ⊆ neighbors m x:= by
    obtain ⟨p,hpK,rfl⟩:= mem_image.mp hk; let A':=Y' p; have hh:= contempt hC he hp (I:=I) (I':=I') A'; have ht' := hx' p hpK
    obtain ⟨hz,hV⟩:= rent (H:=I') A' (((hh.1.trans (congr_arg (verse R.path) (HY p))).trans_le (h.earns _ hpK)))
    refine ⟨mem_biUnion.mpr ⟨_,mem_map_of_mem (disc Y) (show A'∈ v from mem_image_of_mem _ hpK),hz⟩, fun i hi=> ?_⟩; apply (neighbors_mem ..).2; exact (separation_triangle _ (pace Y A') _).trans ((Nat.add_le_add ht' ((neighbors_mem ..).1 (hV hi))).trans ht)
  have hM:Meadow.ground I' v⊆neighbors m x:= by intro i hi; obtain ⟨k,hk,h⟩:= mem_biUnion.mp hi; obtain ⟨s,hs,rfl⟩:=mem_map.mp hk; exact (hr s hs).2 h
  have ht': Set.InjOn (verse_down P) v:= fun i hi j hj hh=> (nest_mint (hC:=hC) (he:=he) (h:=by assumption) (H:=H) (Q:=Q)).point hm x i j ((neighbors_mem ..).1 (hM (hr i hi).1)) ((neighbors_mem ..).1 (hM (hr j hj).1)) hh
  have hL:wrappers P v=z:= by unfold wrappers v; rw [Finset.image_image,show verse_down P ∘ Y'=id from funext HY,image_id]
  exact ⟨v,(crew_port hC he hp (I:=I) (I':=I') v ht' ((garden hC x hm).mono (coe_subset.mpr hM))).2 (hL.symm ▸ h),hM,hL⟩

variable (ht:T'=Deck.re T) (hq:R'.p= R.p) (hζ:R'.beta=R.beta) (χ:Chi) (A:Config G c) (ha:RG.flags (Pressure.temp p) A=∅)
local notation "Z" => splitter (Deck.divides hC)
include ht hq hζ ha χ
lemma rendition (π k : ℕ) (hr: d+τ ≤ m) (hm:4*m < c.val) : Nonempty (ExchangeP (Z) (steady I π k) (steady I' π k) χ x ((L).low.links A) A d m) := by
  let Γ (i:I'.ThinP) (j:I.ThinP) := ∃ z:Park C F,Crew I' π k z ∧ I'.smallAt i ⊆ neighbors m x∧ i.val=hatch Y z ∧ j.val=hatch S (wrappers (L) z)
  have heq:2*m<c.val:=by omega
  have hx:= garden hC x heq; have hΩ {z} (hb : Crew I' π k z) (hv: Meadow.ground I' z⊆ neighbors m x):= crew_port (π:=π) (k:=k) hC he (I:=I) hp z (agency hC he x heq hb hv) ((garden hC x heq).mono (Finset.coe_subset.mpr hv))
  refine ⟨⟨Γ,fun i hi hy=> ?_,fun j hj hz=> ?_,?_,?_,?_,?_⟩⟩
  · obtain ⟨z,h,r⟩:= steady_mem.1 hi; obtain rfl : i=activeM h:= Subtype.ext r
    have hy' : Meadow.ground I' z⊆neighbors m x:= hy.trans (fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega)))
    have hv:= (hΩ h hy').1 h; exact ⟨activeM hv,steady_mem.2 ⟨_,hv,rfl⟩,_,h,hy',rfl,rfl⟩
  · obtain ⟨z,h,r⟩:= steady_mem.1 hj; obtain rfl : j=activeM h := Subtype.ext r
    obtain ⟨v,hv,hV,hz⟩:= meets_home (I':=I') hC he x hp z h hz hr heq
    exact ⟨activeM hv,steady_mem.2 ⟨_,hv,rfl⟩, hV, v,hv,hV,rfl, (congr_arg (hatch S) hz).symm⟩
  · rintro i j k ⟨z,hz,hZ,h,r⟩ ⟨v,hv,hv',g,h'⟩; have he:z=v:=Finset.map_injective (disc (Y)) (h.symm.trans g); rw [he] at r; exact Subtype.ext (r.trans h'.symm)
  · rintro i j k hx hy ⟨z,hz,hZ,h,r⟩ ⟨v,hv,hV,g,h'⟩; have hett : i=activeM hz:=Subtype.ext h; rw [hett] at hZ; have hs b (hh:b∈z):separation x (pace Y b) ≤ m:= (neighbors_mem ..).1 (hZ (center_ticket hz b hh))
    have hu : k=activeM hv:=Subtype.ext g; rw [hu] at hV
    have ht := genitive hC he x heq hs (fun i hi=> (neighbors_mem ..).1 (hV (center_ticket hv i hi))) (Finset.map_injective (disc S) (r.symm.trans h'))
    exact Subtype.ext (h.trans ((congr_arg _ ht).trans g.symm))
  · rintro i j ⟨z,hz,hQ,h,hp'⟩; rw [show i=activeM hz from Subtype.ext h] at *; change I.unionP j.val= _; rw [hp']; exact pitched hC he hp (I:=I) (I':=I') z
  rintro i j ⟨z,hz,hQ,h,hp'⟩; obtain rfl : i=activeM hz:= Subtype.ext h; rw [hp']; have hk:Meadow.ground I' z⊆_:=(show I'.smallAt (activeM hz)⊆ neighbors m x from hQ); exact meetups hC he I' I ht hp hq hζ x m (by omega) (agency hC he x heq hz hk) hk hz.earns A χ ha hz.hot ((hΩ hz hk).1 hz).hot
end YM.AllOrder.High
