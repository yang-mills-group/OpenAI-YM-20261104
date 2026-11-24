import YM.Juniper.Gauze.Epoch
/-! # Numerical agenda-before-boosts. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Gauze
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Rain Roost
open Progress.DirectedRecipe Time Refrain LocalAtlas Bright
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {L : Side} {c f:Side} {i j N m n:ℕ}
-- combine Boost ALWAYS with Bright.extras. Need pass T fixed ANY from whittle at family constructor.
variable {C: Targets X.p X.K} (D: Rolls X.p) {E: Expenses C}
    {p:Return.Wages}{v : ℕ→ℝ} (R:PhysicalNext.Repeat.Register D E p v) (T : Snip G)
-- PAY exactly flex before local actual.
structure WindowG (G:Gauge) (L:Side) (S:Snip G)(b j:ℕ)(P:RG.Stage)(x:ℝ):Prop where
   earns (r:ℕ) : r≤j → raiseK G L P r j b x ≤ betaK G L r j x ∧ pie G L P r j b x ≤ betaK G L r j x ∧ alarmed G L P r j b x
   rep : reshapeG G L S (Trio.most b) x P.order
   starsX : ∀ B:BudgetPoint,B.threshold≤2*Pressure.fiery G x L→∀ c f: Side, 2*Trio.base b (radiusB x)< c.val→∀ w:ℕ, w+1 ≤ Trio.base b (radiusB x) →∀ (u:2*w≤f.val)(o:Site c) (V:Config G c), Healthy B.threshold (neighbors (Trio.base b (radiusB x)) o) V→ ∃ (z:Site f→ G.El) (t : Positions (Uniform.Primary f G)), actual t=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖t‖+2*Sienna.furl G L x < slim G L x
   seam : ∀ B:BudgetPoint,B.threshold=temp x→ B.threshold≤2*Pressure.fiery G x L → B.order=P.order → ∀ (c:Side)(W: Positions (Uniform.Primary c G)), ‖W‖+2*furl G L x < slim G L x → flags B.threshold (actual W)=∅ → ∀ (q:ℕ→ RegularAddress c)(u:ℕ→ Config G c→ℝ)(H f:Config G c→ℝ) (v b z:ℝ), Meadow.Budget B q u b→ B.Regular univ H→(∀ V∈sunny B,f V=z-H V-Boulevard.throng u V)→
     (∀ W': Positions (Uniform.Primary c G),‖W'‖+2*furl G L x < slim G L x → actual W'∈sunny B→Brush P.order v (slim G L x)⁻¹ ((Boulevard.stillA f)∘actual) W')→
     ∀ l:List (Directions G c), l.length ≤ B.order → (∀ i∈l,‖i‖≤ B.threshold)→ ‖leftDerivs (Boulevard.stillA H) l (actual W)‖≤ ticket P.order v+ 2*((Fintype.card (Site c):ℝ)*b)
lemma forfeit (T:Snip G)(L₀:Side)(b j:ℕ)(S:RG.Stage): ∀ᶠ x in atTop, WindowG G L₀ T b j S x:= by
   let q (r:ℕ)(x:ℝ):= alarmed G L₀ S r j b x
   have he : -(1/2:ℝ)<Gauze.bill:= by norm_num [Gauze.bill]
   have hp (r:ℕ)(h:r≤j) := (sail G L₀ S r j b h).and (chimes G L₀ S r j b h)
   filter_upwards [(Set.finite_Iic j).eventually_all.mpr (fun r h=>hp r h), cashSlim G L₀ T (Trio.most b) (Trio.rows G L₀ b|>.2.2.2.uses) S.order, Gauze.pledgesFlex Gauze.bill he G L₀ (fun x=>Trio.base b (radiusB x)) (Trio.rows G L₀ b|>.2.2.1.uses), Gauze.risingFlex G L₀ Gauze.bill he (show Gauze.bill < -(1/4:ℝ) by norm_num [Gauze.bill]) S.order] with x hf he hh hg using ⟨fun r hr=> and_assoc.mp (hf r hr),he,hh,hg⟩
variable {P:Protection D}
-- no `kitReady` calls when estimator price singular outside Throngs. ANY holds
structure WindowsG (W:Delays P): Prop where
   confirm: LocalAtlas.ConfirmW D R W (widest D C)
   endowed (j i:ℕ) : StepStages j i→∀ x,W.betaEntry j≤ x→ WindowG G (D.L j) T (trek (C j i|>.halo) (mast j)) j (X.p.profile i) x
lemma tonight (V:Delays P) : ∃ W:Delays P, DelayLe V W ∧ WindowsG D R T W:= by
   have hp j i (h:StepStages j i) := ((Set.finite_Iic j).eventually_all.mpr (fun n (_:n∈ Set.Iic j)=> LocalAtlas.climate_w D R (widest D C) j i n h (Trio.circles ..))).and (forfeit T (D.L j) (trek (C j i|>.halo) (mast j)) j (X.p.profile i))
   obtain ⟨f, -,he,h⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i (hi:StepStages j i)=>hp j i hi)); refine ⟨{V with betaEntry:=f},⟨he,le_rfl,le_rfl,le_rfl⟩,fun j i hi x ht r hr=>(h j x ht i hi).1 r hr,fun j i hi x ht=>(h j x ht i hi).2⟩

-- TO call stock.
def chargeG : Legato.Booster G where
   asks S _ _ W:= WindowsG _ S T W
   buy S _ _ W:= tonight _ S T W
   mono h hv:= ⟨fun i j hi x p=> h.confirm i j hi x ((hv.beta _).trans p), fun i j hi x p=> h.endowed i j hi x ((hv.beta _).trans p)⟩
end YM.Juniper.Gauze
