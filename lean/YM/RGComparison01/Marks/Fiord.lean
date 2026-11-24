import YM.RGComparison01.Marks.Estates
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
-- Cap.First linked trajectory.B.Stage. Sponsor.Post charges
structure Surplus (G : Gauge)(L : Side) where
  originBill : Kraal.Floor G L -- annotate new base tape
  growth : ℕ -- marker test.Probe growth in z
  shelter : ℝ→ℝ -- sup on real good for each cardTest at π.Aux normalization
  aperture : ℝ→ℝ -- Probe.Both budgets
  head : Geo G L shelter
  wing : Geo G L aperture

/-- Sponsor of marked leases. May see post-block, general. Arranges
 coefficients then chooses envelopes AT any valid tape. -/
structure SourceLane (G:Gauge)(L:Side) where
  inMark : ℕ -- Test denominator valuation
  outMark : ℕ -- Output.render normalization
  dollars : (k:ℕ) → (y u : ℝ→ℝ) → Geo G L y → Geo G L u → ℝ → (x:ℝ→ℝ) → Geo G L x → Surplus G L
abbrev Stipulation (G: Gauge) := (X:Metals G) → (D:Rolls X.p)→ Targets X.p X.K → ∀ _i j _k _m : ℕ, SourceLane G (D.L j)

namespace Fiord
abbrev workload (s t : ℕ) := s+t
abbrev book (p q q' j n:ℕ) := q+Studio.nBudget p q' j n
abbrev heat (k:ℕ):= 2*(k+1)
-- Geometry.Automatic
abbrev foyer (d b j:ℕ):= Vision.escrow d b (j+3) -- Y upon output
abbrev cap (b B':ℕ):= Meadow.studio b B'
abbrev room (b: ℕ)(t:ℝ):= Trio.base b (radiusB t)
abbrev amp (b:ℕ)(t:ℝ):= cap b (radiusB t)
lemma imprint (Z G B k:ℕ)(h:1 ≤ B): Cabinet.garage (Deck.Mint.width Z B (B+G*B)) k + 3*Deck.Mint.width Z B (B+G*B) ≤ cap (foyer Z G k) B:= by
   apply le_trans _ (Vision.shapes Z G (k+3) B h)
   unfold Vision.Hall Cabinet.studio Cabinet.garage; nlinarith only
lemma spacious (b:ℕ)(t:ℝ): amp b t+(2*amp b t+1)≤room b t∧4*amp b t+16≤ 2* room b t∧ 4*amp b t+16 ≤ (Trio.fence b (radiusB t) 0).val := ⟨by unfold room amp cap Trio.base Trio.tent; omega,by unfold room amp cap Trio.base Trio.tent; omega,Trio.highChair _ _ _|>.1⟩
-- Geometry.Note fee intake Y.Poly
section rate
variable (b k n j q q' p :ℕ) (L:Side) (G:Gauge)
local notation "u"=>room b
local notation "f"=>amp b
abbrev popG (b:ℕ)(t:ℝ):=(Fintype.card (Site (Trio.fence b (radiusB t) 0)):ℝ)
-- Melody Sheets salaries
abbrev cashup (j:ℕ) (v w c:ℝ) := (Boulevard.ticket j (v+v)+ 2*(c*w))+(v + c*w)
lemma music (j:ℕ) (v w c g : ℝ) : cashup j (v*g) (w*g) c = cashup j v w c*g:= by unfold cashup Boulevard.ticket; ring
abbrev missCost (k:ℕ)(v:ℝ):=2*(|v| *(2^(k+1):ℝ))+1 -- κ=2(k+1), schedule g
lemma fee_geo (b k d w q' p' : ℕ) {P V qG F:ℝ→ℝ} (h:Geo G L P)(hp:Geo G L V)(hx:Geo G L F)(hX:Geo G L qG): Geo G L (fun t=> Reels.tab k b d w q' p' (P t) (V t) (qG t) (F t)):= by
   unfold Reels.tab; simp only; exact (Geo.joins (Archival.accepts h.mean _) (Kraal.for_ritual _ _ hX hp)).joins ((Geo.fixed _).times hx)
lemma bookie {P0 W Y:ℝ→ℝ}(h:Geo G L Y)(hp:Geo G L P0)(hw:Geo G L W) : Geo G L (fun t=> cashup j (P0 t) (W t) (Y t)):=
      (((((Geo.fixed _).times (hp.joins hp)).times (Geo.fixed _))).joins ((Geo.fixed _).times (h.times hw))).joins (hp.joins (h.times hw))
variable (V v' D' P U Y X : ℝ→ℝ) (S : RG.Stage)
abbrev missW (k:ℕ)(g h:ℝ):=missCost k g*h^(k+1)
abbrev localCost (t:ℝ) := cashup S.order |Reels.tab k S.order n q q' p (P t) (V t) (U t) (X t)| (missCost k (Y t)) (popG b t)
lemma cordial (h:Geo G L P)(he:Geo G L V)(hp:Geo G L U)(hx:Geo G L X)(hY:Geo G L Y): Geo G L (Fiord.localCost b k n q q' p V P U Y X S):= by
   have he:= fee_geo L G S.order k n q q' p h he hx hp; have hP:Geo G L (fun t=> missCost k (Y t)):= ((Geo.fixed 2).times (hY.mean.times (Geo.fixed _))).joins (Geo.fixed 1)
   exact bookie S.order L G (Loads.voting b L G 0) (he.mean) hP
lemma cordial_pos (t:ℝ): 0≤ Fiord.localCost b k n q q' p V P U Y X S t:= by
   have he:0 ≤ missCost k (Y t):= by unfold missCost; positivity
   let u':= |Reels.tab k S.order n q q' p (P t) (V t) (U t) (X t)|; have ht:0 ≤ u':= abs_nonneg _
   have hw:0≤ popG b t:= Nat.cast_nonneg _; change 0≤ (Boulevard.ticket _ (u'+u')+2*(popG b t* _))+(u'+(popG b t)*missCost k _); unfold Boulevard.ticket; positivity
lemma motoring :Geo G L (fun t=> Rotunda.priceP (Loads.size S 0) (2*f t) (u t+ f t)):= by
   obtain ⟨hp,hq,hv,hU⟩:= Trio.rows G L b
   have h₁:Geo G L (fun t=>(↑(2*f t):ℝ)):= by have he:= (Geo.fixed (G:=G) (L:=L) 2).times (Geo.basic hp); convert he using 2 with x; simp only [Nat.cast_mul (α:=ℝ) 2 (f x),Nat.cast_ofNat]
   have h₂:Geo G L (fun t=>(↑(u t+f t):ℝ)):= by have he:= (Geo.basic hv).joins (Geo.basic hp); convert he using 2 with x; exact Nat.cast_add _ _
   exact (((Geo.fixed 1).joins h₂).power _).times ((Geo.fixed _).times (((Geo.fixed 1).joins h₁).power _))
abbrev Meters (t:ℝ) := Rotunda.priceP (Loads.size S 0) (2*f t) (u t+f t) * localCost b k n q q' p V P U Y X S t
abbrev tollW (t:ℝ) := Diner.Borders.cashier 1 ((S.supportExponent+3) *Trio.coverTicket b) (L.val^4) (u t+f t) n
abbrev fuel (t:ℝ) := Meters b k n q q' p V P U Y X S t*tollW b n L S t
lemma wages (h:Geo G L P)(he:Geo G L V)(hp:Geo G L U)(hx:Geo G L X)(hY:Geo G L Y): Geo G L (fuel b k n q q' p L V P U Y X S):= by
   have hh : Geo G L (Fiord.tollW b n L S):= by
      have hp:Geo G L (fun t:ℝ=> (↑(u t+f t):ℝ)):= by have h := (Geo.basic (Trio.rows G L b|>.2.2.1)).joins (Geo.basic (Trio.rows G L b|>.1)); convert h using 2 with x; exact Nat.cast_add _ _ -- (Geo.basic (Trio.rows G L b|>.2.2.1)).joins (Geo.basic (Trio.rows G L b|>.1))
      unfold Fiord.tollW Diner.Borders.cashier; push_cast
      exact ((((Geo.fixed 1).joins (((Geo.balling hp).times (Geo.fixed _)).times (Geo.fixed _))).power _).times (Geo.fixed _)).times (Geo.fixed _) -- maybe push_cast +*1
   exact ((motoring b L G S).times (cordial b k n q q' p L G V P U Y X S h he hp hx hY)).times hh
end rate
end Fiord
end YM.RGComparison01.Pledge
