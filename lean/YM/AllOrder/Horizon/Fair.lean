import YM.AllOrder.Horizon.Dust

/-! # Pay the ULTRA price (poly cost, all errors) for collective tally. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} (D: Rolls X.p) (C : Targets X.p X.K) {i j:ℕ}
    {P : Protection D}

def columnB (j i : ℕ) (x:ℝ):Prop := let L:= D.L j; let b:= parking (tall i) (C j i).halo; let T:= X.p.profile i; let z:= betaF G x L; let y:= z ^ air i; let h:= Trio.base b (radiusB x)
    y < eaves G L x ∧ (2*gStep z ≤ y) ∧ (∀ k:ℕ,k ≤ i → Real.exp (Trio.stout T * coverTicket b) * priceC G L T b i k x ≤ z^ output k (4*edgeW i)) ∧
    (∀ P:BudgetPoint,P.threshold ≤2*Pressure.fiery G x L→∀ c f: Side, 2*h<c.val→∀ w:ℕ,w+1≤h→∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors h o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), Boulevard.actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*Sienna.furl G L x < y) ∧
   ∀ (P: BudgetPoint), P.threshold=Pressure.temp x → P.threshold ≤ 2 * Pressure.fiery G x L → P.order=T.order → ∀ (c:Side) (W:Positions (Uniform.Primary c G)), ‖W‖+2*furl G L x < y → flags P.threshold (actual W)=∅ → ∀ (S:ℕ→RegularAddress c) (u:ℕ→ Config G c→ℝ) (H f:Config G c→ℝ)
    (v b z:ℝ), Meadow.Budget P S u b→P.Regular univ H → (∀ V∈ sunny P,f V=z-H V-Boulevard.throng u V) →
      (∀ W': Positions (Uniform.Primary c G),‖W'‖+2*furl G L x < y → actual W'∈ sunny P→ Brush T.order v y⁻¹ ((Boulevard.stillA f)∘actual) W') →
    ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l,‖i‖≤P.threshold) → ‖leftDerivs (Boulevard.stillA H) l (actual W)‖ ≤ ticket T.order v + 2*((Fintype.card (Site c):ℝ)*b)
lemma stages : ∀ᶠ t in atTop, columnB D C j i t := by
  let Q:= C j i; let L:=D.L j; let T:= X.p.profile i; let b:= parking (tall i) Q.halo
  obtain ⟨hl,hb⟩:= buys_air i; have h₀:= pledges_slender (e:=air i) hl G L (fun x=>Trio.base b (radiusB x)) (Trio.rows G L b|>.2.2.1.uses)
  have he k (hp:k ≤ i):= ((weightC (G:=G) (L:=L) T hp b).mul_left (Real.exp (Trio.stout T * coverTicket b))) (output k (4*edgeW i)) (by unfold output; linarith [edge_pp i])
  filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 1, h₀,rising_slender G L hl (by unfold vow at hb; linarith) T.order, (glim G L) (air i) hl,(eventually_all_finset (Finset.range (i+1))).mpr (fun k hk=> he k (Nat.le_of_lt_succ (mem_range.mp hk)))] with x hx h₁ hy hf he
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hx hb, (le_abs_self _).trans hf,fun k hk=> (le_abs_self _).trans (he k (mem_range.mpr (by omega))),h₁,hy⟩

abbrev Fair (W:Delays P):= ∀ j x,W.betaEntry j≤x → ∀ i, StepStages j i → columnB D C j i x
lemma climb (V:Delays P) : ∃ U:Delays P, DelayLe V U∧ ∀ W:Delays P,DelayLe U W → Fair D C W:= by
  obtain ⟨x,-,hv,hV⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i hi => stages D C (i:=i) (j:=j)))
  exact ⟨{V with betaEntry:=x},⟨hv,le_rfl,le_rfl,le_rfl⟩,fun Z h j t ht i hi=> hV j t ((h.beta j).trans ht) i hi⟩
end YM.AllOrder.Shop
