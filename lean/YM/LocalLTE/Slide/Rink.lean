import YM.LocalLTE.Fan.Local
import YM.LocalLTE.Tile.Allot
import YM.LocalLTE.Slide.Bisque
import YM.LocalLTE.Tier.Dais
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
open Scarf Refrain Marlin
-- Calendar lives independent R beyond proofs by Cancelling, uses only H.f, Probe.Law.
def excerpt (k:ℕ): Finset (Magazine H):= (Finset.range k).image (fun i=> (pennant H i).2)
def Slice (Q:H.fragrances→Prop) (i: Magazine H) : Prop:= Sum.elim Q (fun _=>False) i
def window (Q:H.fragrances→Prop) (k:ℕ): Finset (Magazine H):= (East.excerpt H k).filter (Slice H Q)
def locker (Q:H.fragrances→Prop) (k:ℕ) : Finset ℕ := (univ ×ˢ (window H Q k)).map (pennant H).symm.toEmbedding
lemma aisle (Q:H.fragrances→Prop) (k:ℕ) (i:ℕ): i∈locker H Q k ↔ (Song.pennant H i).2 ∈ East.window H Q k:=by unfold locker; simp
lemma unfolds (Q:H.fragrances→Prop) (i:ℕ): ∀ᶠ k:ℕ in atTop,Slice H Q (pennant H i).2→ i∈locker H Q k := by
    filter_upwards [eventually_gt_atTop i] with k hx hp using (East.aisle H Q k i).2 (mem_filter.mpr ⟨mem_image_of_mem _ (Finset.mem_range.mpr hx),hp⟩)
variable (Q:H.fragrances→ Prop)
lemma shots (P : BudgetPoint) {t : ℕ}(hv:∀ p: H.fragrances, Q p → East.Orchestra H p ℓ) (ht: stagnate ℓ X.halo * P.B ≤ t) (hh : t≤ j*P.B) (hB:P.B= radiusB s): Scarf.Rooms (Beam.marquee H P).reg (East.locker H Q k) t P j:=by
    refine ⟨hh,fun i hi=>?_⟩
    let v:= (pennant H i).1; obtain ⟨-,he⟩:=mem_filter.mp ((East.aisle ..|>.1 hi))
    have hp : East.Slice H Q (pennant H i).2:= he
    change v.spread (Beam.contents H P (pennant H i).2).support⊆neighbors t (Lattice.affine v.1 v.2 (Beam.contents H P (pennant H i).2).site)
    rcases hk:(pennant H i).2 with p|p; swap; · rw [hk] at hp; exact False.elim hp
    rw [hk] at hp
    let W:= (Beam.dashboard H p).site; have hz : (Beam.contents H P (.inl p)).support=Captain.reachability p:= Beam.see H p; rw [hz]
    have h₁:= Scarf.normRange (s:=v) (x:=Lattice.affine v.1 v.2 W) rfl t
    change _ ⊆ neighbors t (Lattice.affine v.1 v.2 W)
    rw [← (show v.spread (neighbors t W)=_ from h₁)]; apply Finset.image_subset_image
    exact fun k hk=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp (stations H _ _ (hv _ hp) W (hz ▸ (Beam.dashboard H p).anchor) hk)).trans (hB ▸ ht)) -- edit
-- lift Moves
section
variable {χ' : Chi}
lemma packedMoves (P : BudgetPoint) {K:Cash W s a L X o U T R'} (F:Match.Alliance H K 1 0) (θ: Signed)(x:Site c)(g: Magazine H→ Config G c→ ℝ) (k:ℕ):
    let d:= diamond (Beam.marquee H P) (East.locker H Q k) j
    Nonempty ((read H F χ' d.reg (Song.choir g ∘ pennant H)).Moves θ x):=by
    obtain ⟨π⟩:= Beam.moves H P χ' F θ x g; let w:= Song.whirl (ι:=Magazine H) θ x; let P₀:=pennant H
    let T:=read H F χ' (Beam.marquee H P|>.reg) (Song.choir g∘pennant H)
    -- can't use existential reeds as ep. manually
    let y:= Refrain.congo P₀ w
    have h (i:ℕ): P₀ (y i)=w (P₀ i):= Refrain.perch P₀ w i
    have hv (i):= Song.spirit (Beam.contents H P) g θ x (P₀ i)
    let M : T.Moves θ x:= ⟨y,π.kp,(fun i=>?_),(fun i=>?_ ),π.forced_support,π.forced_inventory,π.forced_tests,(fun i U=>?_),π.valuesK⟩
    · intro d; refine Scarf.rotation (X:=Beam.marquee H P) (V:=⟨_,_⟩) θ x (show ((Beam.marquee H P).read ⟨_,_⟩).Moves θ x from M) ?_
      intro i; change i∈East.locker H Q k ↔ y i∈East.locker H Q k; rw [aisle,aisle]; change _∈_ ↔ (P₀ _).2∈_; rw [h]; rfl
    · change (Song.revolve _ (P₀ (y i))).site=_; rw [h]; exact (hv i).1
    · change (Song.revolve _ (P₀ (y i))).support=_; rw [h]; exact (hv i).2.1
    change choir g (P₀ (y i)) U=_; rw [h]; exact congr_fun (hv i).2.2 U
end
end YM.PhysicalNext.Repeat.East
