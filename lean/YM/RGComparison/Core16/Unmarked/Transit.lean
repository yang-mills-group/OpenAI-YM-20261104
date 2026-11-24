import YM.UVExtension.Dales.Pry
import YM.UVExtension.Dales.Corn
import YM.UVExtension.Camp.Plum
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped
/-!
# Extend the domain of the unmarked exact producer in the UV Valve.

It wasn't obvious one could compare with a rendered model within that state: e.g. using `Tour.voy`
would require `Lives` on the incoming model. That would be too expensive: the latter demands an
actual `PeriodFuture` on the real model. Instead unwind the exact theorem (through the
independent-support/sector, `Match.Alliance` and deterministic masking/kernel history -- not
recompute moves). This one step is now *actual* on EVERY eligible presented model in the
iteration norm, whether emanating from the bare density or not. We stress that the steps (Fitted)
are dealing with UNNORMALIZED vacuum, and can be taken even at arguments with a zero gas
on most of the domain, or with a nonpositive gas. The vacuum scalar is read at coarse field = 1 and is valid even
if the incoming gas vanishes on a region. Division later is only when applied on the actual theory
or with new bills; neither needed in this seminorm.

Critical!: this chosen model domain remains a nontrivial constraint on permitted
labels! See Ledger. Not claiming every abstract Wilson-form analytic model is a Valve input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Unmarked
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open UVExtension UVExtension.Guild UVExtension.Concert UVExtension.Camp.Cart
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ} (hm:m<N) {ε:ℝ}
open SectorNext.Vacuum
variable {P P₁:(RG.Rep G (A.B.a.S.side (m+1) n))} (H:Guide A.B R.shape N m n P) (W: Zeal R.target R.shape A N m) (k:ℕ) (h:P₁.p=(A.B.a.budget (m+1)))
variable (J:Item R (P:=P) (N:=N) P₁)

-- Scalar accumulator after support pass, before coupling-Hessian reset.
def τ (O: Return.Wood A.B m n):= Song.weighty J.atH Chi.canonical O - Meadow.barony J.atH Chi.canonical k (A.B.kin.alpha N m) 0 1
variable (T:Crest R ε)(he:Wheeled R H W (ε:=ε) k)
local notation "Q#" => (Fintype.card (Site (A.B.a.S.side m n)):ℝ)
local notation "α" => A.B.kin.alpha N m
local notation "L#" => Item.issue R H W k J
variable (O: Return.Wood A.B m n)
include hm h he
set_option maxHeartbeats 800000
lemma early : (A.B.a.clock.op m n).push P₁.beta P₁.eval = earlyValue (Guild.Market R H) (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) (Item.song R H W k J) P₁.beta (τ R k J O) α := by
    let S:= A.B.a.S; let B:= (A.B.a.budget m); let X:= R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
    let Z:= Beam.marquee H B
    let F := J.links R H
    let C:= plusone H F Chi.canonical α; let z:= (A.B.a.clock.hatBeta m); let r:= (Rain.lint R.target A m)
    let e:= Trio.base r (radiusB z); let U:= Meadow.timbres F α k (χ:=Chi.canonical)
    let f:= W.offers k ⟨P₁.beta,J.aisle⟩; let t:=Trio.ornament (c:=S.side m n) (Rain.screens R.target A m) f
    let u:= Trio.insight B F α k (Rain.screens R.target A m) e f
    let hU:= Song.weighty J.atH Chi.canonical O
    let v:= Meadow.barony J.atH Chi.canonical k α 0 1
    have hA:= Boulevard.lays R.shape A (A.B.a.S.oneStep m n).exact_size F R.inn.chip hm R.pledging.jewels R.pledging.conducts.full ((R.pledging.agenda _ _ (step_paid A.B.a m)).1) (Guild.hp_width R hm P).1 J.price O
    have hx : Meadow.Budget B Z.reg U.logRead (shoal ε A m) := he.helm P₁ J.atH F J.related rfl J.aisle J.price
    have hp := faucet R hm H W k J.atH F rfl J.related J.price J.aisle h
    funext i
    exact (hA.2 i).trans <|
      Marlin.carries B Z e (2*e) U t u i (R:=posting B H) C (fun _=>⟨rfl,rfl⟩) (A.B.kin.path N m) (A.B.a.params m).clip P₁.beta hU α v hp hx (fun i=>Trio.levy B F α k (Rain.screens R.target A m) e f i _ _ hA.1) (fun s b=> Song.motion _ _ F Chi.canonical α s b) (fun s b=>Beam.moves _ _ Chi.canonical F s b _)

-- Density at the true scalar (not only proportion), all L,N clipping. Both powers absolutely
-- as in Steps (not relative to H.β elsewhere). No need Lives of fine R!!
variable (hG:G.Simple)
include hG T
lemma transits : L#.eval=(A.B.a.clock.op m n).push P₁.beta P₁.eval ∧ L#.Lawful (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m) ∧ L#.activities.KBound (A.B.a.budget m) (Return.forcing A.B m):=by
    let a:= A.B.a; let B:= a.budget m; let V:=Item.song R H W k J; let X:= Market R H; let D:=A.B.kin.path N m
    let p:= (a.params m).clip; let F:= J.links R H
    let hU:= α
    let σ:= J.first R H W k
    let P':= Progress.DirectedRecipe.finish D p B (shelves X D B) (branch X D p B V α) σ
    let hS:= (a.clock.op m n).push P₁.beta P₁.eval
    have hp:= standing R hm H W k J.atH F rfl J.related J.price J.aisle h T he hG
    have hl v : (P' v).Lawful (a.params m).width (a.params m).paths (a.clock.loopCap m) (a.clock.allowance m) (a.clock.forcedAllowance m):= ⟨A.B.support.cap N m hm.le,hp.2.1⟩
    refine ⟨?_, hl _, hp.2.2⟩
    let O:= Classical.choice (Tree.select (A.B.a.clock.op m n).ratio (A.B.a.clock.op m n).patch.odd_side)
    let v:= Collection.vac V (τ R k J O)
    have hv := ready R hm H W k J.atH F rfl J.related J.price J.aisle h T he
    have hh: (P' v).eval = hS := by
       refine Eq.trans (funext (fun i=>?_)) (early R hm H W k h J he O).symm
       exact (hp.1.unshifted D p σ v i).trans (hv.raw_evaluator hG (A.B.support.cap N m hm.le) (Guild.hp_width R hm P).1 (Guild.hp_width R hm P).2 α (Return.enough_room ..) P₁.beta (τ R k J O) i)
    have hd : hS 1=Real.exp (v * Q#):= (congr_fun hh 1).symm.trans (flat_density (P' v) (hl v))
    change (P' (Real.log (hS 1)/ Q#)).eval=hS; rw [hd,Real.log_exp,mul_div_cancel_right₀ _ (show Q#≠0 from (site_pos _).ne')]; exact hh
end YM.RGComparison.Core16.Unmarked
