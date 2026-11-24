import YM.Qlocal.CoverLease
import YM.Qlocal.Versal.Missed
import YM.Qlocal.Versal.Tack
import YM.Qlocal.Versal.Billow
/-!
Instantiate the universal primitives at a scheduling lease in the purchased currency.
Available at the Guide for any admitted period & construction-cutoff. Reclosure
trace tickets use the same θ. The support exponent ticket buys at least +3
at this entry, of which +2 is needed for two packings at that step. Strong CP.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Leasing
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
open RGComparison01 RGComparison01.Pledge
open Checks Baked Palette Pillow Resin Season Ink Switch Mallow Ovens OmitClusters Song Refrain Motion Extra.Iteration
open Push.PriceCompiler Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Push.Uniform Sienna Fare Lapis
open Holdings
open Tensor WilsonStartup Presented Planned.JetPort Ovens
open RG.Shoot
variable {M:Metals G}{R':Rolls M.p}{A:Alloy M R'} (F:Roost.Factor A)
    {m N p:ℕ} {η:ℕ→ℝ} {u:ℕ→ℕ}
local notation "C₀"=> A.B.a
set_option quotPrecheck false
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "Y"=> (Mural.sheet M.p R' ((C₀).clock.adm (m+1)))
local notation "x₀"=> (C₀).clock.hatBeta m
local notation "θ"=> (C₀).budget m
local notation "μ₀"=> F.shape.μ J I
local notation "L★"=> R'.L J
local notation "F'"=> (F.target J I)
local notation "ℓ★"=> (F.expense J I)
variable (η) (B':Bauble G (R'.L (A.B.a.clock.J (m+1)))) (hB : Opened F η k j m B')
local notation "s"=> θ.supportExponent
local notation "λ★"=> β -- placeholder
variable (hz:f.val=c.val*(A.B.a.S.block m).val){R:RG.Rep G f} (C:Boulevard.Chartlet F.shape A N m hz R) (hr:Boulevard.SeekR F.shape A N m hz C) (hm:m<N) (hβ:R.beta ∈ band A.B.a (m+1))
    {Ω : Type} {L : ι → Lotus.Leaf R}{D : Ω → ι→ Lotus.Leaf R}
set_option quotPrecheck false
local notation "S★"=> Pane.panel A m hz
local notation "O₀"=>Chi.canonical
local notation "τ"=>(ℓ★).earn
variable [Fintype ι] (h : Roster L D) (g:ι→ℝ) (hx: Bench L g (B'.mass (A.B.a.clock.hatBeta m)))
  (hE: (Tithe.portion R.activities Ψ).EBound R.p e)(he : e ≤ incomingE G (R'.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))
local notation "V!"=>Positions (Uniform.Primary c G)
-- output oracle for regular projection (ANY values; analytic prediction built via Thunder). Stip Ester.
open Stowe Luggage Sienna
variable (Z:Ribbon R n)(ξ:ℕ)(p:Finset ι)(F₀: Ω → Config G c→ℝ) {u0 ν r:ℝ}
noncomputable abbrev scaleM (Y0:Side)(k:ℕ)(e u0:ℝ): ℝ:= B'.miss x₀*e+B'.roi x₀/(Height.grow G L★ x₀)^k+u0 -- conflict Y0 unused
noncomputable def zone (n:ℕ)(i:Side)(ν w:ℝ): ℝ:= (Boulevard.ticket n (ν+ν) +2*((Fintype.card (Site i):ℝ)*w))+(ν+ (Fintype.card (Site i):ℝ)*w)
local notation "H"=> zone (θ).order c ν (Leasing.scaleM (m:=m) B' c k e u0)
local notation "Ψ₀"=> Drawings.desk C Z
-- measure root Property.Yes pure.AUX. estimate on Reels.sunny obtained later. `Gauge` head T(x).C.Flow.News.Weight
include hB hE he hx hβ hm hr h
set_option maxHeartbeats 600000 in
lemma gains (hd:0<u0) (hT:Drawing.Opens Z Ψ) (hl:∀ i,¬ Luggage.long L Z i) (hy:p.card ≤ ξ)(hn:p.Nonempty)
    (h₀ : Sluice.Shore G (R'.L (A.B.a.clock.J (m+1))) (A.B.a.budget m).order (A.B.a.clock.hatBeta m) r) (hV : ∀ x:Ω,(A.B.a.budget m).Regular Finset.univ (F₀ x))
    (hW: ∀ x:Ω,∀ W:Positions (Uniform.Primary c G),‖W‖+2*Sienna.furl G L★ x₀<r→ Boulevard.actual W∈ Boulevard.sunny (A.B.a.budget m)→ Brush (A.B.a.budget m).order ν r⁻¹ ((Reels.allotV (D x) g C p (χ:=O₀)-F₀ x)∘Boulevard.actual) W): (∀ x:Ω,Lanes.Shed C (D x) g (A.B.a.budget m) Chi.canonical) ∧ ∀ᶠ i in atTop,∀ x:Ω,∀ (W:Positions (Uniform.Primary c G)), ‖W‖+2*Sienna.furl G L★ x₀<r →flags (θ).threshold (actual W)=∅ → ∀ l:List (Directions G c), l.length ≤ (θ).order → (∀ i∈l,‖i‖≤ (θ).threshold)→ ‖leftDerivs (Stowe.tale (D x) g C (Drawing.cabinet C Z) (j+ξ) i p (χ:=Chi.canonical)-F₀ x) l (actual W)‖≤ zone (θ).order c ν (Leasing.scaleM (m:=m) B' c k e u0):= by
 let hr':= (resourceT F η B' hB hz C hr hm hβ h g hx hE he (Classical.choice (Tree.select (S★).ratio (S★).patch.odd_side))).2; let he₀:= hr'.1; have hX x:Lanes.Shed C (D x) g θ Chi.canonical:= h.stance C θ _ g he₀.log_all he₀.masking; refine ⟨hX,?_⟩
 filter_upwards [accounts F η B' hB hz C hr hm hβ h g hx hE he Z (fun _=>True) ξ hT (fun _ _ i _=>hl i) hd] with i hi
 intro x W hw hh; have he := h.retag _ _ _ _ x he₀.log_all
 let v2 := scaleM (m:=m) B' c k e u0; have hx': Rooted (origins (D x) C) (Checks.treat (Luggage.miss (D x) C Z ξ (j+ξ) i) (ρ:=g) (χ:=O₀)) θ (τ) (scaleM (m:=m) B' c k e u0):= h.miss C Z θ _ _ _ _ (by simpa only [and_true] using hi) -- adjust
 apply Bridges.proven (D x) g C θ Z p hn rfl rfl (hX x).filtered he (renter _ _ _ hB _ _ hm _ (h.bench x hx)) i (j+ξ) (F₀ x) (hV x) hr'.2 ?_ h₀ hx' W hw hh hy (hW x)
 have hT := C.laws.data.room.temperatures; rw [C.laws.data.funds.length_eq] at hT; exact hT
end YM.Qlocal.Leasing
