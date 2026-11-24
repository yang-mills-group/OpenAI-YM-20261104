import YM.Juniper.Flare.Portrait
/-!
 # Reduce PANEL price, ownership and measurability to a list of genuine *finite-volume* actual kernel estimates against an analytic model

 Analytic needed later. No sector-by-sector re-expression hypothesis used in `Fixed`. Uniform at tiles to unlimited volume occurs here, through all output derivative, hit, threshold meters. Pose orbit from same Frame investments, supports as in Bright. Only require Ward/gauge-invariant TEMPLATE. Not granting budget comparing unnamed model. See `Proxy`.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Rain Roost
open Progress.DirectedRecipe Time Refrain Bright Gauge Gauze
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {c f:Side} {i j N m n r:ℕ}
variable {D: Rolls X.p} {A:Alloy X D} (R : Factor A)
variable {β:ℝ}
local notation "J"=> A.B.a.clock.J (m+1)
local notation "B"=> (A.B.a.budget m)
local notation "B₀"=> (A.B.a.budget (m+1))
local notation "x"=> A.B.a.clock.hatBeta m
local notation "z"=> A.B.a.clock.hatBeta (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "L"=> D.L J
local notation "H"=> mast J
local notation "α"=> A.B.kin.alpha N m
local notation "u!"=> Bright.home R m
local notation "u₁"=> unboxed R m
local notation "O"=> Chi.canonical
local notation "Y"=> caves R m
local notation "V"=> miner R m
local notation "ℒ"=> Meadow.studio V (radiusB x)
local notation "W"=> Mint.width (R.target J I).halo (radiusB x) (radiusB x)
local notation "t!"=> (R.expense J I)
variable (hm:m<N) (hp: f.val=c.val*(A.B.a.S.block m).val) {u:RG.Rep G f}
local notation "k"=> (((z)^deep J+(z)^deep J)+(z)^deep J)
local notation "ζ"=> Cash.armK (R.target J I) L (R.shape.μ J I) x 0 (R.expense J I).degrees
variable (P : Lens R hp N u β) (P': Pages R N m β) (T : Snip G) (h : WindowsG D R.shape T A.delay)
local notation "F"=> plusone P.chart (Bright.blank P.chart) O α
variable {b : ℝ} (Q:∀ i:Stars, Curtain G (caves R m i))
    (he:∀ i:Stars,(Q i).TidyC (A.B.a.budget m) (Meadow.studio (Bright.miner R m) (radiusB (A.B.a.clock.hatBeta m))) b)
local notation "K!"=> (X.p.profile I)
local notation "Ψ"=> (2*minds (K!).order (clouds G L J r x))
local notation "Lp"=> Bright.lighted R m
local notation "f₀"=> fun i:Stars=> Flare.stage R (Bright.sews R m i) (P'.books i) n
local notation "q"=> fun i:Stars=> (Q i).root
local notation "v!"=> Flare.ScheduleCost R m
local notation "τ"=> (fun i:Stars => T) -- unused
local notation "E₁"=> pie G L K! r J V x
local notation "L'"=>sews R m
noncomputable def small (i:Stars) := LensLog (A:=A) (N:=N) (u:=(P'.offer i)) (β:=β) (sews R m i)+Trio.froth ((Q i).root)

-- local estimates needed only on Pose. Condition w.r.t. coarse tensor topology, not whole path. Later strengthen only *pre-later levels* demands on charts for calculus. No need budgets on Π* beyond those at post curtain itself.
def Fixed (r:ℕ) : Prop :=
    let d:= 2*minds (K!).order (clouds G L J r x)
    ∀ i:Stars, ∀ P: Positions (Uniform.Primary (Y i) G), ‖P‖ + 2*furl G L x < slim G L x → actual P ∈ sunny B→ Brush (K!).order d (slim G L x)⁻¹ ((Boulevard.stillA (Flare.small R P' Q i)) ∘ actual) P

variable (hF: Fixed R P' Q r)
local notation "v"=> portraits R P' Q
-- exact form signs
include hm he hF h
lemma neighbors_price (i:Stars)(hC:Collection.Local (posting B (P'.books i).chart) B (Flare.chest R (sews R m i) (P'.books i) n) v! ζ) (p:Positions (Uniform.Primary (Y i) G)) (hp:flags (B).threshold (actual p)=∅)(hv:‖p‖+2*furl G L x<slim G L x)
    (l:List (Directions G (Y i)))(hl:l.length ≤ (B).order)(hL:∀ a∈l,‖a‖≤(B).threshold):
    ‖leftDerivs (Boulevard.stillA (Trio.froth ((f₀ i)-(q i)))) l (actual p)‖ ≤ courseK G L K! r J V i x:= by
    obtain ⟨ho,hp',hz,hτ⟩:=Rain.jersey (A:=A) (m:=m); let X':=P'.books i; let f:=Trio.froth ((f₀ i)-(q i)); let S:=Classical.choice (Tree.select (panel A m (sews R m i)).ratio (panel A m (sews R m i)).patch.odd_side)
    obtain ⟨g,hg,hgp⟩:= hC.cheap; let σ:= weighty (X'.chart) O S * (Fintype.card (Site (caves R m i)):ℝ); unfold courseK; rw [show inkK G L (K!) J x=v! from (by dsimp only [Flare.ScheduleCost, inkK]; rw [hτ, PriceCompiler.beta_eq A.B.valid])]
    refine ((Gauze.palace R T h).seam B rfl ?_ ho (caves R m i) p hv hp _ (Flare.chest R (L' i) X' n).logRead f (small R P' Q i) Ψ v! σ ⟨g,hgp,fun j=> ⟨hC.smooth _,hg j⟩⟩ ?_ ?_ (hF i) l hl hL)
    · exact (P'.books i|>.chart).laws.data.funds.length_eq ▸ (P'.books i|>.chart).laws.data.room.temperatures
    · rw [show f=∑ j:Site (Y i), ((f₀ i) j-(q i) j) from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j _=> CouplingShape.reg_sub (CouplingShape.reg_extend ((Flare.score R _ _ hm n j).1) (subset_univ _)) (CouplingShape.reg_extend (Curtain.pose (he _) j) (subset_univ _))
    intro V' hV; have hC:= Flare.collectively R hm (L' i) X' S V' (smoky hV) n; unfold small f; simp only [Trio.froth,Pi.add_apply,hC,Pi.sub_apply,sum_sub_distrib]
    unfold σ; change (_- _- _)+_= _; ring

variable (hc:2*Bright.home R m < c.val)
-- use USEFUL φ estimate local. no πA-cancellation except legitimate rooms. Cuts use for all health, no need choose stricter inside estimates here.
include hc
lemma widths (hC:∀ i:Stars,Collection.Local (posting B (P'.books i).chart) B (Flare.chest R (sews R m i) (P'.books i) n) v! ζ) : Meadow.Budget B (Marlin.leap u! (c:=c)) (portraits R P' Q n) E₁:= by
    have hH:= Gauze.palace (m:=m) R T h
    obtain ⟨ho,hp',hz,hτ⟩:= Rain.jersey (A:=A) (m:=m)
    let f:=f₀ - q; let U := ornament (c:=c) (Lp) f; have heq:portraits (c:=c) R P' Q n=U:= Gauze.ornamentSub Lp _ _
    have hs(i:Stars)(j:Site (Y i)):(B).Regular univ (f i j):= CouplingShape.reg_extend (CouplingShape.reg_sub ((Flare.score R _ _ hm n j).1) (Curtain.pose (he _) j)) (subset_univ _)
    have ht':u₁+4≤u! := by unfold Bright.home Trio.base unboxed; omega
    rw [heq,← Gauze.hue G L K! r J V B (Gauze.made (A:=A) (m:=m))]
    refine Bright.esteem (B).B_pos (V) _ (Gauze.uniform R _ hs) (fun i=>?_) (show u!≤2*u! from by omega) rfl
    refine Trio.kinds _ _ _ _ hs (fun i=> Gauze.currency hH.rep.1.le) ht' (furl G L x) (slim G L x) _ ?_ (fun i=> neighbors_price R hm P' T h Q he hF i (hC i))
    intro V' hV i; have hz: (B).threshold ≤2*Pressure.fiery G x L:= (P'.books i|>.chart).laws.data.funds.length_eq ▸ (P'.books i|>.chart).laws.data.room.temperatures; exact hH.starsX _ hz c (Y i) hc (u₁+i.val) (by unfold Trio.base unboxed; have h:=i.isLt; omega) ((Lp i).ge) _ V' hV
end YM.Juniper.Flare
