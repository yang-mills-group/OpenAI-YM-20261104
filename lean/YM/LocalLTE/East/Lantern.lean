import YM.LocalLTE.Slide.Villages
import YM.LocalLTE.Tile.Allot
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
open Scarf Refrain Marlin Opera
variable {ε :ℝ}
-- Norms θ. δ ref covers in output.Including p>J. Lambda(q) at epoch natural price. Income skip.
def bloom (x:ℝ)(k:ℕ) := x^(k/ (100:ℝ)) -- inverse extra
lemma bloom_nn (hp:0≤v) (k:ℕ):0 ≤ East.bloom v k:= Real.rpow_nonneg hp _
lemma bloom_rise (hp:1≤v) (k:ℕ) {p:ℕ}(h:k≤p): East.bloom v k≤ East.bloom v p:= Real.rpow_le_rpow_of_exponent_le hp (by exact div_le_div_of_nonneg_right (Nat.cast_le.mpr h) (by norm_num))
lemma bloom_bill {v:ℝ} (h:1≤v) (m:ℕ):1≤ East.bloom v m:=Real.one_le_rpow h (by positivity)
lemma bloom_price (i:ℕ)(v:ℝ)(hv:0<v): East.bloom v i * v^(chip i) = v^(-(11/10):ℝ):=by unfold East.bloom; rw [← Real.rpow_add hv]; unfold chip; ring_nf
private lemma noteOne {α:Type}{t:Finset α}{f:α→ℝ}(h:∀ i∈t,1≤f i){i:α}(hv:i∈t): f i≤∏ i∈t,f i:= by
   rw [← Finset.mul_prod_erase t f hv]; exact le_mul_of_one_le_right (zero_le_one.trans (h i hv)) (Finset.one_le_prod (fun i hi=>h i (mem_of_mem_erase hi)))
lemma toll (F:ℕ→ℝ)(hp:∀ i,1≤F i)(p:H.fragrances): 1≤Height.rocket H F p:= one_le_prod (fun _ _=> surge_one hp _)
lemma toll_imp (F:ℕ→ℝ)(hp:∀ i,1≤ F i)(p:H.fragrances) (z:ℕ)(j)(h: Opacity.key S z∈ (p.2 j).val): F z≤ Height.rocket H F p:=by
   refine le_trans (b:= Height.surge F S (p.2 j).val) ?_ (noteOne (f:=fun i=> Height.surge F S (p.2 i).val) (fun _ _=> surge_one hp _) (mem_univ j)) -- name edit
   refine noteOne (f:=Height.hip F S) (fun i he=> ?_) h
   cases i; exact le_rfl; exact Silica.lip_one F hp _
variable (P:BudgetPoint) (χ:Chi) (p:ℝ)
-- Semantic valuations SELECT p filter for multi-variable amplification. All paths. Mask-local support native
structure Voices (D:ℕ→ℝ) : Prop where
   budgets: ∃ f:H.fragrances→ℝ, (∀ i,Height.ancestry i → P.Regular (Beam.dashboard H i).support (Song.sequence H (Meadow.intern H) χ i)∧ P.supBounds (Beam.dashboard H i).site (Beam.dashboard H i).support (Song.sequence H (Meadow.intern H) χ i) (f i))∧
       Quotes.early P (Beam.dashboard H) (fun i=> if Height.ancestry i then Height.rocket H D i*f i else 0) p
-- receive `visage`
lemma voyage (p' p₀ s':ℝ)(he:p'+p₀≤p)(hn:preExponent P ≤ s') (D:ℕ→ℝ)(hD:∀ i,1≤D i)
   (hp:∃ f₁ : H.fragrances → ℝ, (∀ i:H.fragrances, Height.ancestry i → P.Regular (Beam.dashboard H i).support (Song.sequence H (Meadow.intern H) χ i)∧ P.supBounds (Beam.dashboard H i).site (Beam.dashboard H i).support (Song.sequence H (Meadow.intern H) χ i) (f₁ i)) ∧
    let X₀ (z:H.fragrances):=if Height.ancestry z then rocket H D z * f₁ z else 0
    early P (Beam.dashboard H) (fun z=> if z∈Set.range (Brim.icon H)∧ Beam.nearbound z then X₀ z else 0) p'∧
    Ac.Hit (Captain.reachability (H:=H)) P.B (fun z=> if z∈Set.range (Brim.icon H)∧ Beam.nearbound z then 0 else X₀ z) s' p₀): East.Voices H P χ p D:=by
   obtain ⟨f,h,hF⟩:= hp; dsimp only at hF
   have hx(z:H.fragrances)(hz: Height.ancestry z): 0≤rocket H D z*f z:= mul_nonneg (rocket_pos H D hD _) (h _ hz).2.1
   have he' z: (Beam.dashboard H z).support=Captain.reachability z:= Beam.see H z
   refine ⟨f,h,fun x=> budget_loosen (budget_mono (budget_plus (hF.1 x) (hF.2 x)) (fun i=> ?_) (fun i=> ?_)) he⟩
   · dsimp only; split_ifs
     next _ he => exact mul_nonneg (hx _ he) (Real.exp_nonneg _)
     next => rw [zero_mul]
     exact le_rfl
   dsimp only; split
   next hi=>
     have hz:x∈Captain.reachability i:= hi ▸ (show _∈_ from he' i ▸ (Beam.dashboard H i).anchor)
     rw [if_pos hz]; split_ifs
     any_goals simp only [zero_mul,add_zero,zero_add,le_refl]

     rw [he']; apply mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg _))) (hx _ (by assumption))
   next => exact add_nonneg (le_refl 0) (hF.2 x |>.1 i)
-- E revenue filter. unrot cost.
lemma riseBirth (q:H.fragrances→Prop) (v:ℕ→ℝ)(_hv:∀ i,1 ≤ v i) (hr:Voices H P χ p v)(a:ℝ) (hc:0 < a)(he:∀ i,q i→ Height.ancestry i∧ a≤Height.rocket H v i):
    Meadow.Budget P (Beam.dashboard H) (fun i=> if q i then sequence H (Meadow.intern H) χ i else 0) (a⁻¹*p):= by
     obtain ⟨f,hF,h⟩:= hr.budgets; let g' i:=if q i then f i else 0
     have hw i: q i→0≤ f i:= fun h=>(hF _ (he i h|>.1)|>.2.1)
     refine ⟨g',fun i=> budget_mono (budget_scale (inv_nonneg.mpr hc.le) (h i)) (fun x=> ?_) (fun x=> ?_),fun i=>?_⟩
     · dsimp only; unfold g'; split_ifs
       next _ h=> exact mul_nonneg (hw _ h) (Real.exp_nonneg _)
       next => rw [zero_mul]
       exact le_rfl
     · have ht:= (budget_scale (inv_nonneg.mpr hc.le) (h i)).1 x; dsimp only at ht ⊢; split
       next hx=>
          rw [if_pos hx] at ht
          unfold g'; split
          next hz=>
             rw [if_pos (he _ hz|>.1), ← mul_assoc a⁻¹ _ (Real.exp _)]
             apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _); apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (he _ hz|>.2) (hw _ hz)) (inv_nonneg.mpr hc.le)); exact le_of_eq (inv_mul_cancel_left₀ hc.ne' _).symm
          next hz=> exact (zero_mul _ |>.le).trans ht
       rw [mul_zero]
     dsimp only; unfold g'; split
     next hz => exact hF _ (he _ hz|>.1)
     next hz => exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! CouplingShape.sup_const (p:=P) (X:=(Beam.dashboard H _).support) (o:=(Beam.dashboard H _).site) (G:=G) 0⟩

end YM.PhysicalNext.Repeat.East
