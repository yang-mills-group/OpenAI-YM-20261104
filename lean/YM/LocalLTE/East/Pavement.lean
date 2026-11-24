import YM.LocalLTE.East.Podium
/-! Orbit radius inward. -/
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
include H
lemma places (m:ℕ)(p:Site c) : coverNumber (radiusB s) (neighbors (m*B) p) ≤ ballCost m:=by
    -- need radius pos
    refine (Corona.cover_mono ?_ B).trans (Corona.tile p m B (Brim.paidB H))
    intro i hi; exact halo_spec.mpr ⟨p,mem_singleton_self _,(neighbors_mem ..).1 hi⟩
def pubFee (L:Side)(G:Gauge)(r ℓ b:ℕ):ℝ:= ((ballCost (stagnate ℓ r * b):ℝ)* Census.tubularPrice G L)
include H
lemma caps (v:H.fragrances) (he:East.Orchestra H v ℓ) (i) : ((LocalLTE.Fan.Field.pin (East.docket H v i) H).card:ℝ) ≤ pubFee L G X.halo ℓ B:=by
    obtain ⟨x,hx⟩:=(v.2 i).property.1; have hP:=stations H ℓ v he x (mem_biUnion.mpr ⟨i,mem_univ _,hx⟩); set P:= neighbors (stagnate ℓ X.halo*B) x
    have hY: H.unionP (LocalLTE.Fan.arm (East.docket H v i)) ⊆ P:= by
        rw [← (he.each i).lift]; intro y hy; exact hP (mem_biUnion.mpr ⟨i,mem_univ _,hy⟩)
    have hc: LocalLTE.Fan.Field.pin (East.docket H v i) H ⊆ univ.filter fun x=> Census.along (G:=G) S x∈P := by
        intro y hy; apply Finset.mem_filter.mpr; exact ⟨mem_univ _, hY ((mem_filter.mp hy).2 _ (by simp))⟩ -- edit
    have hh:= (Finset.card_le_card hc).trans ((Census.entering S) P)
    unfold pubFee; rw [H.laws.data.funds.length_eq] at hh; exact_mod_cast hh.trans (Nat.mul_le_mul_right _ (neighbors_card ..))
local notation "ξp"=> betaF G s L
variable (Z:ℕ→ℝ)(r₁:ℕ→ℕ)(κ:ℝ)(bk k₂:ℕ)
lemma hatching (p:H.fragrances)(h:East.Orchestra H p ℓ)(he:∀ i m,Sum.inl m∈ East.docket H p i→ r₁ m≤k₂ ∧ TellerF R (ξp) κ bk (r₁ m) (Z m) m) : ∀ i k,k∈ East.docket H p i→ Breed R r₁ Z (ξp) κ bk B k₂ k:=by
    intro i k hk; rcases k with k|k
    · exact he _ _ hk
    have hz:=(h.each i).stretch k hk; rcases k with k|k|k|k <;>first| exact hz| trivial
lemma title (p:H.fragrances)(h:East.Orchestra H p ℓ):∃ i k, Sum.inl k∈East.docket H p i:=by
    obtain ⟨i,k,hz⟩:=h.ancestor; refine ⟨i,k,?_⟩; unfold East.docket East.lining; exact Finset.mem_preimage.mpr hz

variable {P:Teller G} {v₀ v₁ K₁:ℝ}
-- Purchase Precision for any INPUT poly grade order x≤f cutoff. Radius OUT strictly > ℓ geometry.
open LocalLTE.FrameBox LocalLTE.Inset Brush Sienna
end YM.PhysicalNext.Repeat.East
