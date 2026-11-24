import YM.UVExtension.Spire.Spark
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped
/-!
 # Exact identity on an actual step for **arbitrary** Valves, including model+the physical K's

 Removing the `Lives` hypothesis (calls the pre-assembly launches, not Tour.voy)
 so that the contraction of E can use evaluated data in the StepData.push
 domain, independent of any ability to reconstruct a given model FROM upper
 levels. Uses the real kernel and β of that input. Pointwise. Scalar adjustment
 even in case (input) not known positive. No Cauchy on the physical coupling.
 Part A iteration script: reuse EXACT same construction shape/reset/costs.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Native
-- imports/argument adaptations from Rain.Glazing & Guild.Run. Thanks to the
-- UV-extension path-keeping architecture this uses no postulate of a stronger
-- analytic estimate.
open UVExtension
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
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Dales
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ}{ε:ℝ}
local notation "B" => A.B.a
local notation "p" => A.B.a.budget m
local notation "T" => A.B.a.clock.op m n
variable (hG:G.Simple) (t:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)
    {x: Valve (m+1) n A.B.a d}{β:ℝ}(hx : Reality A.B.a (m+1) n d x β) (a:ℝ)
local notation "Y!"=> mount R N (m+1) n x.val β a
local notation "X!"=> H.atTopH
local notation "Ω" => Chi.canonical
local notation "Z" => H.speck R d hx a
local notation "G!"=> A.B.kin.path N m
local notation "f"=> (A.B.a.params m).clip
local notation "k"=> H.k
local notation "ρ"=> A.B.kin.alpha N m
local notation "Yd" => H.oracle R d hx a
local notation "S!"=> Guild.Market R X!
local notation "R!"=> Item.song R X! H.W H.k Yd
set_option maxHeartbeats 900000 in
lemma bill_exists : ∃ v:ℝ, ∀ U, earlyValue S! G! f p R! β v ρ U=(T).push β (Y!).eval U:= by
  let W:=Yd; let X₀:=X!; let F:=W.links R X₀; let U:= W.atH
  let P:= Beam.marquee X₀ p; let S₀:= posting p X₀; let Q:= plusone X₀ F Ω ρ; let y:=k; let xk:= R!
  have ht:= W.related; have hf:= W.price; have hi:= step_paid B m
  have hu:= W.aisle
  let H':= R.pledging; have hc:= Guild.hp_width R H.hm Y!; let Y:= Classical.choice (Tree.select (T).ratio (T).patch.odd_side)
  obtain ⟨hV,hF⟩:= Boulevard.lays R.shape A (A.B.a.S.oneStep m n).exact_size F R.inn.chip H.hm H'.jewels H'.conducts.full (H'.agenda _ _ hi).1 hc.1 hf Y
  have hp:= faucet R H.hm X₀ H.W k U F rfl ht hf hu rfl
  have hX:= H.hr.helm Y! U F ht rfl hu hf
  let v : Trio.Offer G (A.B.a.S.side m n):= GleamV R H.W k hu; let b:= SightV R X₀ H.W k U F hu; let q:= Meadow.timbres F (χ:=Ω) ρ k
  let z:=Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)); let K:= bison q v b
  let l:= weighty U Ω Y
  refine ⟨l-Meadow.barony U Ω k ρ 0 1,fun x=> ?_⟩
  have hh:= Marlin.carries p P z (2*z) q v b x («R»:=S₀) Q (fun _=> ⟨rfl,rfl⟩) G! f β l ρ (Meadow.barony U Ω k ρ 0 1) hp hX
    (fun x=> Trio.levy p F ρ y (Rain.screens R.target A m) z (H.W.offers k ⟨β,hu⟩) x _ _ hV) hV.transforms (fun s b=> Beam.moves _ _ Ω _ s b _)
  exact hh.symm.trans (hF x).symm

include hG t
-- Exact positive at flat output even for MIXED INPUT not otherwise positive
lemma synthetic : (Z).eval = (T).push β (Y!).eval ∧
    0<(T).push β (Y!).eval 1 ∧
    (Z).Lawful (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m) ∧
    (Z).activities.KBound p (Return.forcing A.B m) := by
  let F:=Yd; let V:=R!
  let P':=Z
  have hc:= Guild.ready R H.hm X! H.W k F.atH (F.links R H.atTopH) rfl F.related F.price F.aisle rfl t H.hr
  obtain ⟨hy,hz,hT⟩:= Guild.standing R H.hm X! H.W k F.atH (F.links R H.atTopH) rfl F.related F.price F.aisle rfl t H.hr hG
  let Q(a:ℝ):= finish G! f p (Collection.shelves S! G! p) (Collection.branch S! G! f p V ρ) (F.first R X! H.W k) a
  obtain ⟨j,h⟩ := bill_exists R H d hx a
  let y:=Collection.vac V j
  have he: (Q y).eval=(T).push β (Y!).eval := by
     refine funext fun i=> ?_
     exact (hy.unshifted G! f (F.first R X! H.W H.k) y i).trans ((hc.raw_evaluator hG (A.B.support.cap _ _ H.hm.le) (Guild.hp_width R H.hm Y!).1 (Guild.hp_width R H.hm Y!).2 ρ (Return.enough_room ..) β j i).trans (h i))
  have hp (x): (Q x).Lawful (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m):= ⟨A.B.support.cap _ _ H.hm.le,hz⟩
  have hZ (x): (Q x).eval 1 = Real.exp (x * Fintype.card (Site (A.B.a.S.side m n))):= SectorNext.Vacuum.flat_density (Q x) (hp x)
  have hv: flatRate B m n Y! =y := by
    unfold flatRate
    rw [show (T).push (Y!|>.beta) (Y!).eval=(Q y).eval from he.symm,hZ,Real.log_exp]
    exact mul_div_cancel_right₀ _ (SectorNext.Vacuum.site_pos _).ne'
  exact ⟨(hv.symm ▸ he : (Q (flatRate B m n Y!)).eval = _),congr_fun he 1 ▸ hZ y ▸ Real.exp_pos _,hp _,hT⟩
end YM.Juniper.Native
