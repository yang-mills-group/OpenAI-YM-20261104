import YM.LocalTaylorR2.Reel.Threading
import YM.LocalTaylorR2.Orbit.Trunk
import YM.LocalTaylorR2.Reel.Breeze
/-! # Family endpoint — includes *summable* cumulative local reset/scalar error in physical currency and iterative application -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical
open Recoil Capstone Strand Rain Roost Mallow PhysicalNext.Repeat.Legato UVExtension Spire Orchard Mast Oasis LocalTaylorR2.Marker
variable {G:Gauge}
open Pert.Asymptotics Orbit
set_option quotPrecheck false
abbrev harvest (Δ:Daisy.Charity.RG12.Decal G):= Orbit.modes ((Reel.wheelD G).paired Δ)
variable {C:Family G}{g:G.Simple}{Δ:Daisy.Charity.RG12.Decal G}(U:Couture C g (harvest Δ))
local notation "t"=> U.cost.B.a.clock
local notation "τ"=> U.cost.B.a
local notation "x"=> U.cost.B.a.clock.hatBeta
local notation "χ"=> Chi.canonical
local notation "V"=> U.uses
local notation "H"=> U.factor
local notation "X"=> U.uses.realBeat 0
local notation "u"=> Orchard.beam0

abbrev waveScope (N n m:ℕ)(hm:m<N):= Marker.beam H V (m:=m) (N:=N) (n:=n) hm -- remove p
local notation "⚉" => descend H V
def discrepancy (N n m p:ℕ):= if hm:m<N then
     |(X N n m).beta- βGuess H (waveScope U N n m hm) (u) (descend H V p N n (m+1)) p| else 0
def gaugeDebt (N n m p:ℕ):= if hm:m<N then
     |(X N n m).v-priceGuess H (waveScope U N n m hm) (u) (descend H V p N n (m+1)) p| else 0
-- primary local precision retains after horizon & into all n,N on that C. Scalar per site. Retains all Orbit library endpoint
structure Semester : Prop where
    prelude : Orbit.Library U
    calendar : C.path=spine H V
    semester (p r:ℕ)(hp:3≤ p)(ε:ℝ)(he:0<ε)(hv:ε≤1) : ∀ᶠ m in atTop, ∀ i≥m, (r ≤ ((τ).budget i).order)∧(r ≤ ((τ).budget i).power) ∧
        ∀ (N n:ℕ),i≤N → Affords (X N n i) τ i (⚉ p N n i) (upfront (x i) p ε) ∧
          (Real.sqrt ((V).realBeat 0 N n i).beta)⁻¹= regulatorRun C N n i ∧
          x i^ requested (p+1) ε ≤ (Real.sqrt 2*regulatorRun C N n i)^((p+1:ℝ)-ε) ∧
          ∀ hi:i<N, let f:= waveScope U N n i hi; X N n i=f.result u ∧ Award H f u (⚉ p N n (i+1)) p (upfront (x i) p ε)
    sumsReset (p K:ℕ)(ε:ℝ)(he:0<ε)(hv:ε≤1): ∀ᶠ m in atTop,∀ N n:ℕ,m≤N → ∀ T:Finset ℕ,(∀ i ∈ T,m ≤ i ∧ i<N) →
        let m₀:= Reel.margin p K
        ∑ i∈T,(x i)^K * (gaugeDebt U N n i m₀ + discrepancy U N n i m₀ + upfront (x i) m₀ ε) ≤ zig G * (Real.sqrt 2*regulatorRun C N n m)^((p+1:ℝ)-ε)
section root
include g
-- conversion using actual β band at *this* peak
lemma prize (n N m:ℕ)(hm:m≤N): (Real.sqrt ((V).realBeat 0 N n m).beta)⁻¹= regulatorRun C N n m ∧ ∀ p:ℕ, ∀ ε:ℝ, ε≤1 →
        x m ^ requested (p+1) ε ≤ (Real.sqrt 2*regulatorRun C N n m)^((p+1:ℝ)-ε):= by
   have hh:(Real.sqrt ((V).realBeat 0 N n m).beta)⁻¹=regulatorRun C N n m:= congr_arg (fun T:Family G=>regulatorRun T N n m) U.belongs.symm
   refine ⟨hh,fun p ε hx=> ?_⟩; rw [← hh]; exact coupling_paid p ε hx ((τ).fits.delayed _) (((V).ticking N n (Uses.centerP _)).prices m (by omega) hm).2
end root
variable (hC:C.Makes)
lemma retained (hs:Orbit.Library U): Semester U:=by
   have hV:Mallow.RG12.Earned (ticketD G) U.factor.shape U.cost.delay := fun j z hx i hi=> U.couture _ _ hx _ hi |>.1
   have hk:Mallow.RG12.Earned (checkD G) U.factor.shape U.cost.delay:= fun j z hx i hi=> U.couture _ _ hx _ hi |>.2.2.2.1
   have hw:Mallow.RG12.Earned (wheelD G) U.factor.shape U.cost.delay:= fun j z hx i hi=> U.couture _ _ hx _ hi |>.2.2.2.2.2.1
   have hl (p r:ℕ)(hp : 3 ≤ p) (ε:ℝ)(he:0<ε) : ∀ᶠ m:ℕ in atTop, ∀ k≥ m, p ≤ U.cost.B.a.clock.J (k+1) ∧ 3*CalendarStep.loss (U.cost.B.a.clock.J (k+1)) ≤ ε ∧ r ≤ ((τ).budget k).order ∧ r ≤ ((τ).budget k).power:= by
      apply eventually_atTop.mpr; obtain ⟨k,hk⟩:= eventually_atTop.mp (lasts H V U.cellar p r (ε/3) (by positivity)); refine ⟨k,fun i hi j he'=>?_⟩; obtain ⟨X',hz,hy,hA,hB⟩:= hk j (hi.trans he'); exact ⟨X',by linarith,hA,hB⟩
   have hG(p r:ℕ)(hp:3≤p)(ε:ℝ)(he:0<ε)(hv:ε≤1) : ∀ᶠ m in atTop, ∀ i≥m, (r ≤ ((τ).budget i).order)∧(r ≤ ((τ).budget i).power) ∧ ∀ (N n:ℕ),i≤N→ Affords (X N n i) τ i (⚉ p N n i) (upfront (x i) p ε) ∧ ∀ hi:i<N, let f:= waveScope U N n i hi; X N n i=f.result u ∧ Award H f u (⚉ p N n (i+1)) p (upfront (x i) p ε):=by
      filter_upwards [hl p r hp ε he] with m hh; exact fun i ht=> ⟨(hh i ht).2.2.1,(hh i ht).2.2.2,fun N n hi=> plausible H hV hw hk V p hp ε hv m (fun i hi=> ⟨(hh i hi).1,(hh i hi).2.1⟩) ht hi⟩
   refine ⟨hs,(congr_arg Family.path U.belongs).trans (path_eq H V U.cellar),?_,?_⟩
   · intro p r hp ε he hv; filter_upwards [hG p r hp ε he hv] with m hh; intro i hi; obtain ⟨hr,hp,hR⟩:= hh i hi; exact ⟨hr,hp,fun N n hN=> ⟨(hR N n hN).1,(prize U n N i hN).1,(prize U n N i hN|>.2 p ε hv), (hR N n hN).2⟩⟩
   intro p K ε he hv; let q:=Reel.margin p K; have hp: 3≤q:=by unfold q Reel.margin; omega
   filter_upwards [hG q 1 hp ε he hv] with m hm; intro N n hN T ht m₀
   have hc i (hk:i∈T):
      gaugeDebt U N n i m₀ ≤ upfront (x i) q ε ∧ ((τ).budget i).threshold^2* discrepancy U N n i q ≤ upfront (x i) q ε:=by
      obtain ⟨hh,hv⟩:=ht i hk; obtain ⟨hx,hX⟩:= (hm i hh).2.2 N n hv.le|>.2 hv
      unfold discrepancy gaugeDebt; rw [dif_pos hv,dif_pos hv,hx]; exact ⟨hX.scalar,hX.beta⟩
   apply (Reel.calibrate g (τ) T (fun i hi=>(ht i hi).1) p K hv (gaugeDebt U N n · m₀) (fun i=> discrepancy U N n i q) (fun i hi=> (hc i hi).1) (fun i hi=> (hc i hi).2)).trans
   exact mul_le_mul_of_nonneg_left (prize U n N m hN|>.2 p ε hv) (by unfold zig; apply mul_nonneg (by norm_num); exact tsum_nonneg fun i=> by unfold sizeFar; positivity)

/-- Strict consumer: polynomials of all fixed orders, iterative estimates through
    *same* Family incl every stage's V/horizon library.
  -/
theorem actual (g:G.Simple) (κ:ℝ)(hκ:0<κ)(δ:Daisy.Charity.RG12.Decal G)(F:Extraction.Order) :
    ∃ (C:Family G)(f:Extraction.Order)(T':Table C.book)(W:Spec.Final C (F.refine f) T') (L:EveryPhase.Almanac W) (A:Couture C g (harvest δ)),
    C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=κ ∧ UVExtension.Oasis.Floral (hG:=g) C ∧ (Extraction.Order.mk Extraction.Sequence.full (F.refine f).per).Ordered C T' ∧ EveryPhase.Completed W L ∧ OPE.Facilities C (F.refine f) T' ∧ Semester A:=by
  obtain ⟨C,f,T',W,L,A,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h⟩:=Orbit.eventual_library g κ hκ ((wheelD G).paired δ) F; exact ⟨C,f,T',W,L,A,h₁,h₂,h₃,h₄,h₅,h₆,h₇,retained A h⟩
end YM.LocalTaylorR2.Reel
