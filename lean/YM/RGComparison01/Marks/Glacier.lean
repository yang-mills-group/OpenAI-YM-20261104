import YM.RGComparison01.Marks.Aura
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron Switch Mallow Ovens OmitClusters Song Refrain Motion Luggage Oceanic Extra.Iteration
open Push.PriceCompiler Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Hoboken Stowe SliceRows Push.Uniform Sienna Fare Lapis
open Diner Vision Studio Extra.Iteration
open Fiord Estates Tensor WilsonStartup Presented Planned.JetPort
variable (P:Sponsor G)(U:Stipulation G)
namespace Holdings
variable {X:Metals G} {D:Rolls X.p}{Q:Targets X.p X.K}{E: Expenses Q}{v : ℕ→ℝ} {P₀:Return.Wages}(Z:PhysicalNext.Repeat.Register D E P₀ v)
variable (i j k m:ℕ)(hi : 4 ≤ j)
set_option quotPrecheck false
variable {Θ₀ : Protection D}
-- before-step gates
structure Sought (V:Delays Θ₀): Prop where
  drinks j : 1 ≤ V.growth j
  asked j i (h : StepStages j i) (hp:4≤j) k : 1≤k → k ≤ j → ∀ m≤j, Nonempty (Holdings.Quay P U Z i j k m hp (Rights.eta j) (V.betaEntry j) (V.shells j))
-- quant across budgets.Barycenter
variable (V:Delays Θ₀) (w:ℕ→ℕ→ℕ) (h: ∀ i j,StepStages j i→qualify E i j (w i j)∧w i j≤ (D.L j).val)
include h
lemma spun (i j:ℕ) : ∃ z,∀ᶠ t in atTop, StepStages j i → ∀ (p:4≤j) (n r : Fin (j+1)),1≤n.val→ ∀ k≥z, Nonempty (Holdings.Quay P U Z i j n.val r.val p (Rights.eta j) t k):= by
   by_cases hp:StepStages j i; swap; · simp [hp]
   by_cases hh:4≤j; swap; · simp [hh]
   let Q (t:Fin (j+1) × Fin (j+1))(b k):= Nonempty (Holdings.Quay P U Z i j t.1.val t.2.val hh (Rights.eta j) b k)
   have hx (t:Fin (j+1) × Fin (j+1)):∃ z,∀ᶠ b in atTop,1 ≤ t.1.val → ∀ k≥z,Q t b k:= by
     by_cases hv:1≤t.1.val; swap; · simp [hv]
     obtain ⟨z,hz⟩:= Holdings.office P U Z i j hh hp t.1.val t.2.val hv (w i j) ((h _ _ hp).1) ((h _ _ hp).2) (Rights.eta j) (by unfold Rights.eta; positivity)
     exact ⟨z,hz.mono (fun x he _ k hk=> he _ hk)⟩
   choose z he using hx; refine ⟨Finset.univ.sup z,?_⟩; filter_upwards [eventually_all.mpr he] with t ht h hi n m hx k hk; exact ht (n,m) hx k ((le_sup (f:=z) (mem_univ _)).trans hk)
lemma piled : ∃ T:Delays Θ₀,DelayLe V T ∧∀ R:Delays Θ₀,DelayLe T R → Sought P U Z R:= by
   choose z he using spun P U Z w h
   let g j:= fromMax (fun j i=> z i j) j
   obtain ⟨x,-,hx,hZ⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j atTop _ (fun i (hi:StepStages j i)=> (he i j).mono fun t ht=> ht hi))
   refine ⟨{V with betaEntry:=x,shells:=fun j=> V.shells j+g j,growth:=fun j=>V.growth j+1},⟨hx,le_rfl,fun i=>Nat.le_add_right ..,fun i=>Nat.le_succ _⟩,fun Y h=> ⟨fun j=> (Nat.le_add_left ..).trans (h.growth j),fun j i hi hp k hk hh m hm=> ?_⟩⟩
   have hh':z i j≤Y.shells j:= ((le_fromMax (fun j i=> z i j) hi).trans (Nat.le_add_left (g j) _)).trans (h.shells j)
   exact hZ j (Y.betaEntry j) (h.beta _) i hi hp ⟨k,by omega⟩ ⟨m,by omega⟩ hk (Y.shells j) hh'
omit h
def wants (P:Sponsor G)(U:Stipulation G): Agenda G:=fun _ _ _ _ _ _ _ _ _ _ Z _ _ _ _ _ _ V=> Sought P U Z V
lemma negotiated : (wants P U).Payable:= by
   intro s T Q V W Z hs
   choose b hb using priorBill Z
   let f:= fun i=>fromMax (fun j i=>b i j) i
   refine ⟨f,fun L h D F w B H0 Q₀ r p Y hp θ X => ?_⟩ -- pipeline args
   refine Holdings.piled (X:= UVExtension.Case.provider s T L) P U _ X b ?_
   intro j i hi; exact ⟨hb _ _, (le_fromMax (fun j i=>b i j) hi).trans ((h _).trans (D.large _).need)⟩
end Holdings
end YM.RGComparison01.Pledge
