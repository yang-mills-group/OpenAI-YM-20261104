import YM.LocalLTE.Motion.Half
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
open PhysicalNext.Repeat Roost
open YM.LocalLTE FrameBox Inset PriceCompiler
open LocalLTE.Fan Field Fan.Bakers Vine
variable {κ :ℝ}
-- Provenance: choosing kℓ ANY Era & frozen tag, predictor on proposed R (even if not Live)
variable (j n p i m:ℕ) (R₁ R₂:Rep G f) (hr:R₁.beta=R₂.beta) (hp:R₁.path=R₂.path) (f':ℕ→ℕ)(hh:∀ i':ℕ, f' i' ≤ i → R₁.activities.E i'=R₂.activities.E i')
include hr hp hh
section
variable (Q:H.fragrances) (ht:East.award H f' j n p i Q)
include ht
lemma e_shield (j':Option (Fin Q.fst))(z: LevelsΛ (East.docket H Q j') m)(x:Disk G c)(G₁:Forest S.ratio) (B':Coat T G₁) : Bakers.curlP B' R₁ (East.docket H Q j') X.table (Fan.postponement L s o) (Field.pin (East.docket H Q j') H) x z =Bakers.curlP B' R₂ (East.docket H Q j') X.table (Fan.postponement L s o) (Field.pin (East.docket H Q j') H) x z:=by
     unfold curlP; apply MeasureTheory.integral_congr_ae; filter_upwards with v; unfold songP; apply congr_arg; unfold Bakers.lilies; apply prod_congr rfl
     intro k _; let M:= Field.pin (East.docket H Q j') H; let w:= Pond.spill M v
     have h' : Fan.coming X.table R₁ B' x w k.val = Fan.coming X.table R₂ B' x w k.val := by
          unfold Fan.coming; rw [hr,hp]; cases hf:k.val
          next m=> simp only [Sum.elim_inl]; rw [hh _ (ht.2 j' m (hf ▸ k.2))]
          next=> dsimp only [Sum.elim]
     exact congr_arg (fun u => Bakers.ask u (z k)) h'
lemma wayleaf (w:Option (Fin Q.fst)) (g: LevelsΛ (East.docket H Q w) m)(x:Disk G c): felix H Q χ R₁ w g x = felix H Q χ R₂ w g x:=by
     unfold felix; simp only [likely]; apply congr_arg; apply Finset.sum_congr rfl; intro v _; apply congr_arg; apply Finset.sum_congr rfl; intro j' _; exact e_shield H j n p i m R₁ R₂ hr hp f' hh Q ht w g x _ _
lemma stalk : East.maypole m H f' Q χ i R₁ = East.maypole m H f' Q χ i R₂:= by
         funext x; unfold maypole; apply Finset.sum_congr rfl; intro k _; split; swap; · rfl
         refine prod_congr rfl (fun l hl=> East.wayleaf H j n p i m R₁ R₂ hr hp f' hh Q ht _ _ x) -- order
end
lemma screened (Q:H.fragrances) : East.way m H f' χ j n p i κ R₁ (.inl Q)=East.way m H f' χ j n p i κ R₂ (.inl Q):=by
    unfold East.way; dsimp only [Sum.elim]; split; swap; · rfl
    next ht=> unfold East.offK East.reins East.flying; simp_rw [hr, East.stalk H j n p i m R₁ R₂ hr hp f' hh Q ht]
-- framed
lemma shield : way m H f' χ j n p i κ R₁= way m H f' χ j n p i κ R₂:= by
    funext Q; cases Q with
    | inl Q=> exact East.screened H j n p i m R₁ R₂ hr hp f' hh Q
    | inr z=> -- avoid comparing R₁ R₂ through δ reduction.Use def.
         unfold way; dsimp only [Sum.elim]
end YM.PhysicalNext.Repeat.East
