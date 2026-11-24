import YM.LocalLTE.Rate.Cap
/-! book Y witnesses. Require Ge stage upfront small.M and Fare.Cash.W.Calibration. -/
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
variable {G : Gauge} (L:Side)(Z:RG.Stage) {g ℓ:ℕ}{p ζ e η u t ℒ W' :ℝ}
section
variable (W : Wind g η) {X: Metals G} (D : Rolls X.p) {C:Targets X.p X.K}{Z:Expenses C}{w:Return.Wages}{v:ℕ→ℝ} (R:Register D Z w v) (u:ℕ→ℕ→ℝ) (e':ℕ→ℕ→ℝ) (N:ℕ→ℕ→ℕ)(J:ℕ) {κ K:ℝ}
abbrev Receipt (k:ℕ→ℕ→ℕ→ℕ) (f:ℕ→ℕ→ℕ): Prop:= ∀ j i,StepStages j i → DeckBill (κ:=κ) (C:=C) (Z:=Z) (X:=X) W N J j i (f j i) (k j i)
variable (h₀:∀ j i,StepStages j i →((C j i).rate)< Pastel.mini) (hN:∀ j i,StepStages j i → Coup.wire W.ℓ (C j i).halo ≤ N j i) (hc: Reliable G κ K)

include hc hN h₀
lemma salve : ∃ f:ℕ→ℕ→ℕ,∃ k:ℕ→ℕ→ℕ→ℕ,Coup.Receipt (κ:=κ) (C:=C) (Z:=Z) (X:=X) W N J k f:=by
   choose h f H using fun i j=> show ∃ n:ℕ,∃ f:ℕ→ℕ,StepStages i j → DeckBill (κ:=κ) (C:=C) (Z:=Z) (X:=X) W N J i j n f from by
      by_cases he:StepStages i j
      · obtain ⟨n,f,h⟩:= basket (Z:=Z) W N J hN h₀ hc _ _ he; exact ⟨n,f,fun _=>h⟩
      exact ⟨0,0,fun h=> (he h).elim⟩
   exact ⟨h,f,H⟩
variable {f:ℕ→ℕ→ℕ}{k:ℕ→ℕ→ℕ→ℕ} {Q: Protection D}
variable (ha:∀ i j,0 < u i j) (hx:∀ j i,StepStages j i→voltage (X.p.profile i) (N j i) (3*u j i) ≤ e' j i) (hU: W.q < chip (J+1)) (hS : Receipt (κ:=κ) (X:=X) (C:=C) (Z:=Z) W N J k f)
-- mon select.Shill needs future Herit levels bigger, overpurchase.
structure Sunshine (k:ℕ→ℕ→ℕ→ℕ)(κ:ℝ)(U:Delays Q):Prop where
    clear j i : StepStages j i → ∀ x≥U.betaEntry j, Clear W D R u e' N J j i x (k j i) κ
    shell j i : StepStages j i → 32*(1+N j i) ≤ U.shells j
    growth j i : StepStages j i → 1≤ U.growth j
include ha hx hS hU
omit hc hN in
lemma shines (hF : ∀ j i,StepStages j i → f j i ≤ (D.L j).val)(hΛ:∀ j i,StepStages j i →(Height.gusts (C j i)).choose ≤ (D.L j).val) (V:Delays Q) : ∃ U:Delays Q,DelayLe V U ∧ ∀ Y,DelayLe U Y→ Sunshine W D R u e' N J k κ Y:=by
    let g j i:=32*(1+N j i)
    obtain ⟨b,-,he,hV⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i hi=> Coup.cycles W D R u e' N J -- order h flags inspect
      ha h₀ hx hU j i (k j i) hi (f j i) (hS j i hi) (hF j i hi) (hΛ j i hi)))
    refine ⟨{V with betaEntry:=b,shells:=fun j=>V.shells j+fromMax g j,growth:=fun j=>V.growth j+1},⟨he,le_rfl,fun i=>Nat.le_add_right ..,fun i=>Nat.le_succ _⟩,fun _ hv=>?_⟩
    exact ⟨fun j i hi x hx=> hV j x ((hv.beta _).trans hx) i hi,fun j i hi=> (le_fromMax g hi|>.trans (Nat.le_add_left ..)).trans (hv.shells _),fun j i hi=> (Nat.le_add_left ..).trans (hv.growth _)⟩
end
end YM.PhysicalNext.Repeat.Coup
