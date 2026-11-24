import YM.Gaps1020.Local.Trio
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Renew
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time Rain Mallow Roost UVNext.CouplingReset Daisy.Charity.RG12
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open YM.ConnectedActivityE6.Blaze.Thermal1020
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
variable {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A} {c f L:Side} {m n N ℓ i k d M:ℕ}{l s:ℝ}
variable {Y: UVNext.CouplingReset.In A.B.a m n} (H: Spring R N m n l s Y)(x:Set.Icc l s)
local notation "i0" => A.B.a.clock.J (m+1)
local notation "j0" => A.B.a.clock.J m
local notation "O" => Chi.canonical
local notation "P₀"=> A.B.a.budget m
local notation "Tᴹ" M:max => (fun p:ℕ=> M + 1 ≤ p)
local notation "x₀"=> A.B.a.clock.hatBeta m
local notation "φ"=> A.B.kin.alpha N m
local notation "V₀"=> Y x.val
local notation "W"=> H.H
local notation "E0" => H.H.base
local notation "X0"=> H.H.sister x
local notation "S0"=> Mallow.houseS H x
local notation "C0" => A.B.a.S.side m n
local notation "L0"=> D.L i0
local notation "Γ"=> R.expense i0 j0
local notation "Z"=> Thermal1020.horizonRadius G L0 x₀
variable (h:m<N) (he: Mallow.RG12.Earned (Thermal1020.Shared.markerBudget G) R.shape A.delay) (hM:M ≤ A.B.a.clock.J (m+1))
section auxiliary
include he h hM
local notation "Θ"=> X.p.profile j0
local notation "ℓ₀" => turnFee P₀
local notation "Δ" => ℓ₀ * ((Z^(M+1))⁻¹)
abbrev quota (A:Alloy X D)(m M:ℕ):ℝ:= turnFee (A.B.a.budget m)*((horizonRadius G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)^(M+1))⁻¹)
lemma generalPane (J : f.val = c.val * (A.B.a.S.block m).val) (U U': RG.Rep G f)(S: Chartlet R.shape A N m J U)(T: Chartlet R.shape A N m J U')(i:Match.Alliance S T 1 0)(C:Magazine S→Prop):
    Meadow.Budget P₀ (Beam.marquee S (P₀)).reg (choir (fun j:Magazine S=> if C j then Post.jointE i (Tᴹ M) M O j else 0) ∘ pennant S) Δ:=by
   have h' : JointMarket _ Γ L0 (R.walls i0 j0) (R.shape.μ i0 j0) (R.shape.o i0 j0) Θ i0 x₀:= he i0 x₀ (A.B.valid.pays m) j0 (step_paid A.B.a m)
   obtain ⟨A',a,v,t,d,w,B,q,C',k,N',hN⟩:= h'.cost M hM _ _ _ _ (Pane.ovation A N J h R.pledging.conducts.full) _ _ T
   have hp : preExponent P₀ ≤ (Γ).earn:= by unfold preExponent; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact (R.pledging.agenda _ _ (step_paid A.B.a m)).1
   exact Post.scheduleAt i P₀ (Tᴹ M) N' Γ C hN rfl rfl (Rain.jersey (A:=A) (m:=m)|>.1.le) (Rain.jersey (A:=A) (m:=m)|>.2.1) hp _ (fun _ h=>h)

local notation "z"=> noteX W H.knows x.val
local notation "d'"=> H.ordinal
local notation "V'" i=> Rain.moor R.target A m i
local notation "Y!" i=> H.W.tiers i z
local notation "Z0"=> screens R.target A m
private abbrev selfX (i:Stars): Match.Alliance (Y! i) (Y! i) 1 0:= Match.staple rfl rfl rfl
-- use nutrient at actual `Note`, preserving post indexing even if x nontriv. structures macros w quotation.
def sketches (M:ℕ) (i:Stars):=Post.OfferP.pile d' P₀ (Y! i) (Post.lowCurve (selfX H x i) M O φ)
def unspent (M:ℕ)(i:Stars):=Post.OfferP.pile d' P₀ (Y! i) (Post.couponSet (selfX H x i) (Tᴹ M) M O)
omit he h hM in
lemma spiritCoin : H.W.offers d' z= sketches H x M + unspent H x M:=by
   funext i v; rw [show (H.W.offers d' z i v)=Post.OfferP.pile d' P₀ (Y! i) (plusone (Y! i) (selfX H x i) O φ).logRead v from Meadow.aster O P₀ (selfX H x i) rfl rfl rfl φ d' v,Post.composeCurve (M:=M),Post.OfferP.add]; rfl
lemma dyed (i:Stars):
   Meadow.Budget P₀ (Beam.marquee (Y! i) (P₀)).reg (Post.couponSet (selfX H x i) (Tᴹ M) M O) Δ:=by
   have h:= generalPane (N:=N) h he hM (Rain.panes R.target A m i) _ _ _ _ (selfX H x i) (fun _=>True)
   simp only [↓reduceIte] at h; exact h

local notation "wid"=> Rain.lint R.target A m
local notation "e"=> Trio.base wid (radiusB x₀)
def seatNeed (A:Alloy X D)(l m:ℕ)(v:ℝ):ℝ:= Trio.oroW (A.B.a.budget m) (Trio.base l (radiusB (A.B.a.clock.hatBeta m))) (fun i=> 2*(Fintype.card (Site (fence l (radiusB (A.B.a.clock.hatBeta m)) i)):ℝ)*v)
def cue (M:ℕ):Trio.Offer G (A.B.a.S.side m n):= Trio.ornament Z0 (sketches H x M)
def defect (M:ℕ):Trio.Offer G (A.B.a.S.side m n):= Trio.ornament Z0 (unspent H x M)
omit he h hM in
lemma beacon : beacons W H.knows H.W d' x.val=cue H x M + defect H x M:=by funext u; unfold beacons; rw [spiritCoin (M:=M)]; exact Post.OfferP.adjoin ..
lemma purchaseD (u:Site C0): (P₀).Regular (neighbors e u) (defect H x M u) ∧ (P₀).supBounds u (neighbors e u) (defect H x M u) (seatNeed A wid m Δ):=by
   obtain ⟨-,C,d,v,Y,a,b,r,B,q,k,N',h'⟩:= Vacuum.Markets.certified (R:=R) S0 h he M hM
   have ht:= h'.large; have hv := turnFee_pos P₀; have hP:0 ≤ Δ:= by positivity
   exact Post.OfferP.stitch (k:= tent wid (radiusB x₀)) P₀ u Z0 (unspent H x M) _ (fun i=>Post.OfferP.prices _ P₀ _ (dyed H x h he hM i)) (by unfold Trio.base; omega) (fun i=>mul_nonneg (by positivity) hP)
-- compose paint separately. true scalar bar uses same H sight masks.
def barLow (M:ℕ): ℝ:=Post.OfferP.pile d' P₀ (S0) (Post.lowCurve (Match.staple (H:=S0) (J:=S0) rfl rfl rfl) M O φ) 0 1 -- check staple syntax
end auxiliary
end YM.GapsLocal.Renew
