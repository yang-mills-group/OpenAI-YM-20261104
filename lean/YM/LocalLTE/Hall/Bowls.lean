import YM.LocalLTE.Hall.Ash
/-! Aux burning per star. Gold & Ruby over admitted readers. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Urns
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.LocalLTE.Inset ClockB
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {C:Targets X.p X.K} {Z:Expenses C} {F : ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {p : Return.Wages} {s: Set ℝ} {v:ℕ→ℝ} {R:Register D Z p v} {c f:Side} {κ q η l e w : ℝ} {p' : ℕ} (W:Wind p' η) {m n j k N :ℕ} (hm:m<N)
    (hk:Reliable G κ q) {d:ℕ→ℕ→ℝ}
    (hV:Roof.WorksIn R A.post A.delay S) (hX:Spoke D R W A.post κ d A.delay)
    (h:Rich R (1/16) A.delay)
    (hP: Tenement R A.delay)
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall LocalLTE.Fan Pastel -- order
open LocalLTE.FrameBox.Grove
section across
variable (D C)
def due (k:ℕ)(p:ℕ):ℕ:= (pie k+1)+p
def trimSum (M:ℝ):= ∑ i:Stars,|Slide.ray i| * M
structure Straps (q d x:ℝ) (i j n k:ℕ) (M:ℝ) : Prop where
    paint : Meadowlark D C W i j (due k (X.p.profile j).order) q d x M
    sticks (P:BudgetPoint) : P.power=(X.p.profile j).power→P.order=(X.p.profile j).order→P.threshold=Pressure.temp x→P.threshold≤2*Pressure.fiery G x (D.L i)→∀ (c:Side)(o:Site c), let z:= Trio.base (Trio.resize W.ℓ (C i j|>.halo)) (radiusB x); let m:= n*radiusB x; let β:=betaF G x (D.L i)
     z+1 ≤ m →2*m<c.val → 2*(2*z)≤c.val →∀ (Z:Grove o)(f:Config G c→ℝ), P.Regular (neighbors z o) f → (∀ u: Directions G c,‖u‖ < cone clr β → Brush (Urns.due k (X.p.profile j).order) (trimSum M) 1 (f ∘ Grove.soloV) u) → P.supBounds o (neighbors m o) (f-shave Z z q (pie k+1) f) (β^ (dust k))
variable {D C}
include hk
lemma flying {i j:ℕ} {d':ℝ} (n k:ℕ)(hd:0<d') : ∃ M:ℝ→ℝ,∀ᶠ x in atTop,Straps D C W κ d' x i j n k (M x):=by
    let P:= X.p.profile j; let α:= pie k+1; let V:=Urns.due k P.order; let L:=D.L i
    obtain ⟨M,hM,hu⟩:= Urns.arcR D C W hk i j V hd
    have hr : Rate G L 1 (trimSum ∘ M):= by unfold trimSum; exact sparks G L (fun i=> hM.mul_left |Slide.ray i|) -- edit
    have he:1+clr*(pie k+1:ℕ) < dust k:= by unfold clr dust; unfold chip pie; push_cast; linarith
    have hn: Rate G L 0 fun x=>(↑(n*radiusB x):ℝ):=by push_cast; exact Rate.radius_price.mul_left _ -- edit
    refine ⟨M,?_⟩; filter_upwards [hu,LocalLTE.FrameBox.Hall.prunes G L P.order P.power α hn hk (by norm_num [clr] : -(7/16:ℝ)≤clr) (by norm_num [clr]) hr he] with x hu hv
    refine ⟨hu,fun Q hp hi hQ hT c o ht he h Z f hf hg=>?_⟩; have hw:= hv Q hp hi hQ hT _ _ le_rfl ht c o he h Z f hf 1 zero_le_one (by simpa using! hg)
    rwa [one_mul] at hw
end across
end YM.PhysicalNext.Repeat.Urns
