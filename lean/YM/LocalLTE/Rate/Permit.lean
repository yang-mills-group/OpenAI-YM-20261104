import YM.LocalLTE.Rate.Season
/-! Input syntactic permission.Held in retain.U geometry through all turns. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Coup
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Urns
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.LocalLTE.Inset ClockB Scarf East LocalLTE.Fan Pastel
variable {G : Gauge}{c f L: Side} {X: Metals G} {D:Rolls X.p} {C : Alloy X D} {x y κ a:ℝ} {p:ℕ}
variable {S:StepData c f}{T:Tube G S} {R:Rep G f}{P:Teller G}
-- one-law. error slot P+1.Aprices paid.W.r.o Held coefficient.
structure License (p:ℕ) (R:Rep G f) (κ x:ℝ) (tag:ℕ→ℕ) (z:ℕ) : Prop where
    bills : Pumps R (fun i=> bloom x (tag i)) (x^(chip 0))
    crop (i:ℕ)(hi:tag i ≤ p) : ∃ k≤ z,YM.LocalLTE.FrameBox.Polynomial k κ (R.activities.reg i).site (pie (tag i)) (R.activities.E i)
    room {i:ℕ}(hi:tag i ≤ p) : R.activities.E i≠0 → (R.activities.reg i).support⊆ neighbors z (R.activities.reg i).site
-- Calendar Grade price at CURRENT τ (even out of band). extents. Uniform shifted B from WorksIn.
section
variable {tag:ℕ→ℕ} {z : ℕ}
lemma comply (h : License p R κ x tag z)(hv:1 ≤ x) (j:ℕ) (hk:z ≤ j) :∃ φ:ℕ→ℝ,
    (∀ (u : Site f), SumBudget (fun i=> if (R.activities.reg i).site=u then φ i else 0) 1) ∧
    (∀ i, tag i≤ p→ TellerF R x κ j (tag i) (φ i) i) ∧ ∀ k :ℕ,tag k ≤ p → R.activities.E k ≠0→ (R.activities.reg k).support⊆ neighbors j (R.activities.reg k).site:=by
    let f':=tag; let Z:=x^(chip 0); have hx:0<x:=zero_lt_one.trans_le hv; have hz:0 < Z:= Real.rpow_pos_of_pos hx _
    obtain ⟨hh,g,hp,hq⟩:= h.bills; let φ (i:ℕ):=Z⁻¹*(bloom x (tag i)*g i)
    have he i:0 ≤ bloom x (tag i)*g i:= mul_nonneg (zero_le_one.trans (hh _)) (hp _|>.1)
    refine ⟨φ,fun i=> ?_,fun i hk'=>?_,fun i hi hp j hj=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp (h.room hi hp hj)).trans hk)⟩
    · refine budget_loosen (budget_mono (budget_scale (inv_pos.mpr hz|>.le) (hq i)) (fun i=> ?_) (fun i=> ?_)) ((inv_mul_cancel₀ hz.ne').le)
      · split; next=> exact mul_nonneg (inv_pos.mpr hz|>.le) (he _)
        exact le_rfl
      split; next=> exact mul_le_mul_of_nonneg_left (R.p.loMass _ _ (he _)) (inv_pos.mpr hz|>.le)
      rw [mul_zero]
    obtain ⟨K,hK,hz'⟩:=h.crop i hk'; refine ⟨⟨K,hK.trans hk,hz'⟩,VerifiedReset.sup_le (hp _ ) ?_⟩
    have h':Z=bloom x (tag i)*x^(chip (tag i)):= by unfold Z; rw [bloom_price _ _ hx,Coup.chip_zero]
    have hφ : g i= φ i*x^(chip (tag i)):= by unfold φ; rw [mul_assoc,mul_right_comm (bloom ..), ← h', ←mul_assoc,inv_mul_cancel₀ hz.ne',one_mul]

    apply le_trans (le_of_eq hφ) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hv (le_add_of_nonneg_right (by norm_num [Pastel.slack]))) (show 0 ≤ φ i from mul_nonneg (inv_pos.mpr hz|>.le) (he i)))
end
-- calendar n extents.POST eventual. Need trans f at origin.
def CeilingExtent (N : ℕ→ℕ→ℕ) (j:ℕ) := max (N j j) (N (j+1) j)
lemma overhead (N: ℕ→ℕ→ℕ){i j:ℕ} (h:StepStages j i) : N j i ≤ CeilingExtent N i:=by
   rcases h with ⟨h,hp⟩; by_cases h:i=j
   · subst i; exact le_sup_left
   have he:j=i+1:= by omega
   rw [he]; exact le_sup_right
variable {m n:ℕ}{N:ℕ→ℕ→ℕ}
lemma forecast_ge (h: ∀ j,2*CeilingExtent N j≤ (D.L j).val): CeilingExtent N (C.B.a.clock.J (m+1))*((C.B.a.budget (m+1)).B) ≤ (D.L (C.B.a.clock.J (m+1))).val *(C.B.a.budget m).B:=by
    let j:= C.B.a.clock.J (m+1); have ht:= h j
    have hv: (C.B.a.budget (m+1)).B≤ 2*(C.B.a.budget m).B:= by
      let B:=C.B
      have hp := C.prices.1 j (first_le C.B.valid (m+1)) _ (C.B.valid.pays m)
      let N := (C.B.a.budget (m+1)).B; let n := (C.B.a.budget m).B
      have he : N^2 ≤ 2*n^2 := by
        change Stock.scaleB (C.B.a.clock.hatBeta (m+1))^2 ≤ 2*Stock.scaleB (C.B.a.clock.hatBeta m)^2
        rw [beta_eq C.B.valid]; exact hp
      change N ≤ 2*n; nlinarith
    apply le_trans (Nat.mul_le_mul_left _ hv); rw [← Nat.mul_assoc,mul_comm (Coup.CeilingExtent ..) 2]; exact Nat.mul_le_mul_right _ ht
end YM.PhysicalNext.Repeat.Coup
