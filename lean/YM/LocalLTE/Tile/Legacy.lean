import YM.LocalLTE.E6.Dossier
import YM.LocalLTE.Tile.Cups
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Camp
/-! Local LTE high-order representation/compatibility on supported tiles. Adapts
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Camp`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Reserves
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {J₀ M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p

abbrev ownedN (H : Cash W p a L₀ X o U T R) (i:PoetN J₀ H): H.fragrances:= vintageN i.val i.property
def boothsN (J₀:ℕ) (H : Cash W p a L₀ X o U T R) : PoetN J₀ H ↪ H.fragrances:= ⟨ownedN H,enrollmentN⟩
lemma entryN (z: H.ThinP) (h : Height.Elder J₀ z) (hp : ∀ x∈z.val, Beam.Pennies S x) (hv: H.shapeW z.val≤ B):
    ∃ b: Park c f, ∃ X: SeedN H J₀ b,z=HeirN b X:= by
  let k := disc S; let b:= z.val.preimage k k.injective.injOn; have hf i:i∈b↔k i∈z.val:=Finset.mem_preimage
  have he: hatch S b=z.val:= by
    ext y; constructor
    · intro hy; obtain ⟨x,hx,rfl⟩:=mem_map.mp hy; exact (hf _).1 hx
    intro hy; obtain ⟨i,rfl⟩:= (penned ..).1 (hp y hy); exact mem_map_of_mem k ((hf _).2 hy)
  refine ⟨b,⟨he.symm ▸ h.connects,?_,?_⟩, Subtype.ext he.symm⟩
  · have hx:= h.few; rw [← he,hatch,card_map] at hx; exact hx
  intro i hi; have hu:= (hf i).1 hi
  refine (Nat.cast_le (α:=ℝ)).mp ?_ -- change
  refine le_trans ?_ hv; change _≤ Finset.sum _ _; apply le_trans _ (Finset.single_le_sum (fun v hv=> ?_) hu)
  swap
  · obtain ⟨w,hw⟩: v∈Set.range (disc S):= (penned ..).1 (hp v hv); subst v; exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · change (Mint.verse R.path i:ℝ)≤_ + (exCharge T R (note i):ℝ); rw [Mint.balance T R i]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
lemma remnantsN (u:H.fragrances) (ht : ¬ Height.tiredN H J₀ u) (U : Config G c) (hx : Blaze.March.stream H χ U u ≠0) (hn : ¬Height.ancestry u):
    u∈ Set.range (boothsN J₀ H):= by
  obtain ⟨he,hs'⟩:= Height.aging hx ht
  choose b Hk Hv using fun i=> entryN (u.2 i) (he i) (fun j hj=> Height.secular hx ht hn i j hj) (he i).pays
  have hg: StirN H J₀ ⟨u.fst,b⟩:= by
    refine ⟨hs'.le,Hk,fun h=>hx ?_⟩; unfold stream Gas.term; rw [show coefficient H.seam u.snd=_ from ?_,zero_mul,zero_div]
    apply Eq.trans _ h; apply movement; intro i j; rw [Hv,Hv]; apply or_congr; · exact ⟨seed_heightN _ _,fun h=>Subtype.ext (congr_arg (Mint.hatch S) h)⟩
    exact Iff.rfl
  refine ⟨⟨⟨u.fst,b⟩,hg⟩,?_⟩; change Sigma.mk u.fst _=u; congr 1; exact funext fun i=> (Hv i).symm

section shape
variable (v: Match.Alliance H I 1 0) (hr : R.path=R'.path) (he:v.units= Equiv.refl _)
-- supportP may differ in reg otherwise, so assume canonical matches from controller
variable (hp : H.supportP=I.supportP)
include hr hp
lemma estateN (z: Park c f): SeedN H J₀ z ↔ SeedN I J₀ z:= by
  constructor
  · intro h; refine ⟨hp ▸ h.hot,h.sizes,fun i hi=>?_⟩; rw [← hr]; exact h.earns i hi
  intro h; refine ⟨hp.symm ▸ h.hot,h.sizes,fun i hi=>?_⟩; rw [hr]; exact h.earns i hi
lemma universalN (z: Vines c f): StirN H J₀ z ↔ StirN I J₀ z:= by
  have hx:Meadow.ground H=Meadow.ground I:= funext fun i=> by unfold Meadow.ground Cash.unionP; rw [hp]
  exact ⟨fun h=>⟨h.small,(fun i=> (estateN hr hp _).1 (h.each i)),hx ▸ h.moves⟩,fun h=>⟨h.small,(fun i=>(estateN hr hp _).2 (h.each i)),hx.symm ▸ h.moves⟩⟩
def firstBatchN : PoetN J₀ H≃PoetN J₀ I:=Equiv.subtypeEquiv (Equiv.refl _) (universalN hr hp)
include he
lemma identifiesN (z:PoetN J₀ H): v.furrow (boothsN J₀ H z)=boothsN J₀ I (firstBatchN hr hp z):= by
  obtain ⟨⟨i,k⟩,hz⟩:=z; change Sigma.mk i _=Sigma.mk i _; congr 1; funext j; apply Subtype.ext; change v.units (hatch S _)= _; rw [he]; rfl
lemma holdingsN (i:H.fragrances): i∈Set.range (boothsN J₀ H) ↔ v.furrow i∈Set.range (boothsN J₀ I):= by
  let V:= firstBatchN (J₀:=J₀) hr hp; constructor
  · rintro ⟨u,rfl⟩; exact ⟨V u,(identifiesN v hr he hp u).symm⟩
  rintro ⟨u,hu⟩; obtain ⟨u,rfl⟩:= V.surjective u; exact ⟨u,v.furrow.injective ((identifiesN v hr he hp u).trans hu)⟩
end shape
end YM.PhysicalNext.Repeat.Meadow
