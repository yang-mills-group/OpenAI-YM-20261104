import YM.AllOrder.Transit.Clock
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Transit
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm
open Burn Carillon Cap Rosary.Repair Moon Moon.Kit
open Floe
open Step PlanV
variable {G:Gauge}{X: Metals G} {D: Rolls X.p} {C' : Targets X.p X.K} {Z :Expenses C'} {p:Return.Wages} {v:ℕ→ℝ} (R : Repeat.Register D Z p v) {i j:ℕ}
variable {P:Protection D}
local notation "U₀"=> X.p.profile i
local notation "N₀"=> X.p.profile j
local notation "Q!"=> C' j i
variable (d: Roots (G:=G) X.p.profile X.K X.p.kernel)(s:d.Tab D)
local notation "u"=> (C' j i)
local notation "e"=> (Z j i)
local notation "ρ"=> (R.o j i)
set_option quotPrecheck false
local notation "w"=> Shop.parking (Shop.tall i) (C' j i|>.halo)
local notation "Y"=> R.μ j i
local notation "L"=> D.L j
local notation "α"=> (1+cloak D j)
structure Glimmer (j i k:ℕ) (t:ℝ) : Prop where
    burn : Burns R k t j i (X.p.profile i).order (X.p.profile i).power -- N≥W.order for release equals profile
    post : Buoyant G (D.L j) (X.p.profile i) (1+cloak D j) k (Shop.parking (Shop.tall i) (C' j i|>.halo)) t
    lasso : ∀ (B:BudgetPoint),Time.Same (X.p.profile j) B→B.threshold=temp (betaF G t (D.L j))→ B.B=radiusB (betaF G t (D.L j))→ Capacity G B (betaF G t (D.L j)) k
    kind : ∀ (hp:StepStages j i)(hF:4≤j)(hk:Burn.horizon k+2≤ i)(hs:Nonempty (Card D d j i hF (Burn.horizon k))), Figure d D s hp hF (C' j i) (R.o j i) (R.μ j i) k hk hs t
lemma gleams (h:StepStages j i)(hg:G.Simple)(hk:Turbine X.p X.K Z X.p.floorL)(hf:(Z j i).wanting=-(7/16))(ht:(C' j i).table=X.O)(k:ℕ)(h0:k≤ i): ∀ᶠ t in atTop,Glimmer R d s j i k t:=by
 have hx: (u).rate < -(3/8:ℝ):= (Z j i|>.reach).trans (by rw [hf]; norm_num)
 let v t := ∀ (hp:StepStages j i)(hF:4≤j)(hk:Burn.horizon k+2≤ i)(hs:Nonempty (Card D d j i hF (Burn.horizon k))), Figure d D s hp hF u ρ Y k hk hs t;
 have he : ∀ᶠ t in atTop, v t:= by
    by_cases hp : 4≤j; swap; · exact Eventually.of_forall fun x _ h=> (hp h).elim
    by_cases ht':Burn.horizon k+2 ≤ i; swap; · exact Eventually.of_forall fun x _ _ h=> (ht' h).elim
    by_cases he: Nonempty (Card D d j i hp (Burn.horizon k)); swap; · exact Eventually.of_forall fun x _ _ _ h=> (he h).elim
    exact (Kit.house d D s h hp u ρ Y (R.consumes j i h).2.1 ht k ht' he hg).mono fun x hx _ _ _ _=>hx
 filter_upwards [he, wakes R hk h h0 (U₀).order (l:=(U₀).power) hx, forecasted G L U₀ α k w (by have he:=Shop.cloak_gt D j; linarith), (Work.E09.betaF_growth G L).eventually (Burn.worth G k N₀)] with t hi ht hw hp; exact ⟨ht,hw,fun B h hm hz=> hp _ hm hz h.2.2 h.2.1 h.1, hi⟩ -- args
-- include post currencies H move E→V actor. Post K dimension.Do.
variable (W:Return.Wages)(C:Programs X.p)(E:Return.Wages)(r:ℕ→ℕ→ℕ)(q:ℕ→ℕ→JointLoad.Heir.Record) {F:ℕ→ℕ→Postage}(A:Time.Scouts (F:=F))(κ:ℕ→ℕ→Chi)
open Progress.DirectedRecipe
structure Noon (j i:ℕ)(t:ℝ): Prop where
    veracity : Real.exp 1 ≤ t
    sizing : radiusB (betaF G t (D.L j)) ≤ 2*radiusB t
    pearl : ∀ k ≤ i, Glimmer R d s j i k t
    postcard : X.p.first ≤ i → Crisp R W C q r E κ j i t
    pays : let y:=betaF G t (D.L j); let b:=(F j i);
        ∀ β,inBand y β → Payments.Rates (radiusB t) (Real.exp (-Payments.Pairing.kGoal b y β)) ((A j i).pair.strong y β) (t^(-(1/3:ℝ))) (Payments.Pairing.kGoal b y β)
lemma late (g:G.Simple)(hS : Needed X.p X.K Z W X.p.floorL)(hj:StepStages j i)(ht:(C' j i).table=X.O)(hz:(Z j i).wanting=-(7/16))(hf:0≤ E j i)(hp:X.p.first ≤ i → (q j i).ε ≤1/4): ∀ᶠ t in atTop, Noon R d s W C E r q A κ j i t:= by

 have ht:= gleams R d s hj g hS.acts hz ht; have he : ∀ᶠ t in atTop, X.p.first ≤ i → Crisp R W C q r E κ j i t:= by
    by_cases he:X.p.first≤ i; · exact (mates R W C q r E κ g hS.hair (hp he) hf hj).mono fun i' hi h=> hi
    exact Eventually.of_forall fun t hx=> (he hx).elim
 filter_upwards [he,(Filter.eventually_all_finset (Finset.range (i+1))).mpr (fun k hk=> ht k (by have hp:=mem_range.mp hk; omega)), PostP.strong (G.slopeConstant*Real.log (D.L j).val) (A j i) (YM.Work.E04.shift_nonneg G (D.L j)), eventually_ge_atTop (Real.exp 1), (Push.AbsoluteSums.Fees.horizons G (D.L j) 1 (show (0:ℝ)<1 from zero_lt_one) zero_le_one (by norm_num : (2:ℝ) *1 < 4))] with t hh hZ hp he hSize; exact ⟨he,hSize.2.1, fun i hh=> hZ i (mem_range.mpr (by omega)), hh, fun β hb=> hp _ hb _ le_rfl⟩
structure Tour (W': Delays P):Prop where
    actors : ∀ t j i,W'.betaEntry j ≤ t → StepStages j i → Noon R d s W C E r q A κ j i t
    volumes : ∀ j,120 ≤ W'.shells j∧ 2≤ W'.growth j
    wanting : ∀ j i, StepStages j i → (Z j i).wanting=-(7/16:ℝ)
lemma predicts (g:G.Simple)(hS : Needed X.p X.K Z W X.p.floorL)(ht:∀ j i,StepStages j i→(C' j i).table=X.O)(hz:∀ j i,StepStages j i→(Z j i).wanting=-(7/16))(hf:∀ j i,StepStages j i→0≤ E j i)(hp:∀ j i,StepStages j i→X.p.first ≤ i → (q j i).ε ≤1/4) (V:Delays P) : ∃ W':Delays P, DelayLe V W'∧∀ V',DelayLe W' V'→ Tour R d s W C E r q A κ V':= by
 obtain ⟨t,-,hx,hy⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i hi=> Transit.late R d s W C E r q A κ g hS hi (ht _ _ hi) (hz _ _ hi) (hf _ _ hi) (hp _ _ hi)))
 exact ⟨{ V with betaEntry:=t,shells:=fun j=>V.shells j+120,growth:=fun j=>V.growth j+2},⟨hx,le_rfl,fun i=> Nat.le_add_right ..,fun i=>Nat.le_add_right ..⟩,fun Z h=>⟨fun t j i he hi=> hy _ _ ((h.beta j).trans he) i hi, fun j=> ⟨(Nat.le_add_left 120 _).trans (h.shells j), (Nat.le_add_left 2 _).trans (h.growth j)⟩, hz ⟩ ⟩
-- contractor actual.V.Lo. next.
end YM.AllOrder.Transit
