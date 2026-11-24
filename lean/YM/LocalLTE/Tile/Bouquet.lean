import YM.LocalLTE.Tile.Comes
import YM.LocalLTE.Tile.Legacy
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Blox
/-! Local LTE high-order representation/compatibility on supported tiles. Adapts
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Blox`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {J₀ M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p

def keepN (I : Cash W p a L₀ X o U T R') (J₀:ℕ) (i: Magazine I): Prop:= i.elim (fun i=>i∉Set.range (boothsN J₀ I)) (fun i=> B< arc T.down i)
def bouquetN (I:Cash W p a L₀ X o U T R') (J₀ k:ℕ): Finset (Magazine I):= disjSum ((Meadow.calendarN J₀ I k).map (boothsN J₀ I)) ((univ ×ˢ (ripened T.down B k)).map (rollers c).toEmbedding)
lemma notKeptN (z:Magazine I) (h:z ∈ bouquetN I J₀ m) : ¬keepN I J₀ z:= by
  unfold bouquetN at h; rcases z with z|z
  · obtain ⟨i,hi,hz⟩:= mem_map.mp (inl_mem_disjSum.mp h); exact fun he=> he ⟨i,hz⟩
  obtain ⟨⟨s,i⟩,hi,hz⟩:= mem_map.mp (inr_mem_disjSum.mp h); have ht : arc T.down z≤ B:= by rw [← (show legs s i=z from hz),arc_receipt]; exact (mem_filter.mp (mem_product.mp hi).2).2
  exact fun h=> not_lt.mpr ht h
lemma unfurlsN (z:Magazine I) (hp:¬keepN I J₀ z): ∀ᶠ m in atTop,z∈bouquetN I J₀ m:= by
  rcases z with z|z
  · change ¬z∉_ at hp; obtain ⟨w,rfl⟩: z ∈ Set.range (boothsN J₀ I):= Classical.byContradiction hp; filter_upwards [retiresN w] with m hm; exact inl_mem_disjSum.mpr (mem_map_of_mem _ hm)
  obtain ⟨⟨s,i⟩,hv⟩:= (rollers c).surjective z
  have h: Meadow.melody T.down i≤ B:= by rw [← arc_receipt T.down s i, show legs s i=z from hv]; exact le_of_not_gt hp
  filter_upwards [burgeoning T.down B i h] with m hm; exact inr_mem_disjSum.mpr (mem_map.mpr ⟨(s,i),mem_product.mpr ⟨mem_univ _,hm⟩,hv⟩)

def debrisN (I:Cash W p a L₀ X o U T R') (J₀ k:ℕ) (w:ℕ) := ¬keepN I J₀ (Song.pennant I w).2∧ (Song.pennant I w).2∉ bouquetN I J₀ k
lemma dissolvedN (I:Cash W p a L₀ X o U T R') (w:ℕ): ∀ᶠ k in atTop,¬debrisN I J₀ k w := by
  by_cases h:keepN I J₀ (Song.pennant I w).2
  · filter_upwards with k using (fun hx=> hx.1 h)
  exact (unfurlsN _ h).mono fun k h H=> H.2 h


end YM.PhysicalNext.Repeat.Meadow
