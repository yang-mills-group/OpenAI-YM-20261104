import YM.Qlocal.Parabola.Garden
import YM.AllOrder.Transit.Refuge
import YM.Qlocal.Gale
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
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm JointLoad.Clockwork
open Burn Carillon Cap
open Rosary.Repair
open Transit Transit.Moon Transit.Moon.Kit
open Floe Floe.StateE
open Step PlanV Roost
variable {G:Gauge}{X:Metals G}{D:Rolls X.p} (R: Roots (G:=G) X.p.profile X.K X.p.kernel) (Q:R.Tab D)(A:Alloy X D)(F:Factor A)
namespace WheelP
variable {m n k N:ℕ} (h:Pass R Q A F)
local notation "S"=> X.p
set_option quotPrecheck false
local notation "a"=> A.B.a
local notation "C"=> X.p.profile
local notation "E"=>A.B.a.clock.J m
local notation "Y"=> A.B.a.clock.J (m+1)
local notation "V"=> A.B.a.budget m
local notation "y"=> A.B.a.clock.hatBeta m
local notation "L"=> D.L Y
local notation "t"=> betaF G y L
local notation "s"=> (C E)
local notation "W"=> A.B.a.budget (m+1)
local notation "B"=> radiusB y
local notation "g"=> A.B.a.S.block m
local notation "T"=> F.target Y E
local notation "P!"=> (F.expense Y E)
local notation "p"=> A.B.a.params m
local notation "z"=> Burn.horizon k
variable (g0:G.Simple)(hm:m<N)(hk:Burn.horizon k+2≤ A.B.a.clock.J m)
local notation "G0"=> Shop.parking (Shop.tall E) ((T).halo)
local notation "Δ0"=> 1+cloak D (Y)
local notation "δ"=> (A.B.a.params m|>.width)
variable (X': Card D R (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.adm (m+1)) (Burn.horizon k))(hh:Journey R A (m:=m) (N:=N) X') -- syntax
local notation "Ω"=> litP R A Q hk X'
local notation "Plead"=> lead R Q A hk X'
local notation "W'"=> (C Y)
local notation "fφ"=>R.pre z Y
set_option quotPrecheck false
local notation "E'"=> A.B.kin.alpha N m
-- real.Seeds. preserve Bills uses true Guide & Vern.R.Actual Progress.Period
variable (x:ℝ)(hx:x∈ band A.B.a (m+1))
local notation "f"=>A.B.a.S.side (m+1) n
local notation "c!"=> A.B.a.S.side m n
local notation "S★"=> A.B.a.clock.op m n
local notation "Y!"=> Pane.panel A m ((A.B.a.S.oneStep m n).exact_size)
local notation "π"=> (A.B.a.S.oneStep m n).exact_size
local notation "Φ"=>goldN R Q A hk X' x
variable {U: RG.Rep G (A.B.a.S.side (m+1) n)} (hu:U.beta=x)
    (hp:Lives A.B.bake N (m+1) n U) (C₁:Burn.Seed U (M0 k 0 (A.B.a.budget (m+1)) (X'.extra) x))
    (hu':Candor (A.B.a.budget (m+1)) U.activities (Set.range C₁.model) (silver (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1))))) (young (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) k))
    (K:Guide A.B F.shape N m n U)(hc:Opera.Price A.B F.shape N m n U K)
local notation "M"=> Set.range C₁.model
local notation "h′"=> LinkPat A F π K k M
local notation "Γ"=> A.B.kin.alpha N m
local notation "Θ"=> poem R A F X' π x K C₁
local notation "Op"=> Chi.canonical
local notation "v★"=> (heap G s (1/16)*young t k)
local notation "V₀"=> 2*v★
-- Pointwise period induction on actual path. Leaves refinement/b horizons inside Knot.Window (C cap-per-horizon). For correlated across L.Path pay records Step.W.S for all m≤N. Art formula.Unsupervised.
variable (Xξ : Org.Bolt A)

variable (hW : Graces.Nest F Xξ)
local notation "Γ₀"=> Xξ.history N n (m+1)
local notation "Γ₁"=>Xξ.history N n m
local notation "β"=> (Γ₀).beta
local notation "βp"=> (Γ₁).beta
local notation "Mi"=> goldN R Q A hk X' β
open Qlocal
/-- unmarked RG descent that has both strong addressed charges & same exact step FI β guide. -/
def Costly (m N n:ℕ) (U':RG.Rep G (A.B.a.S.side m n)) (U:RG.Rep G (A.B.a.S.side (m+1) n)):Prop:=
  ∃ (K: Guide A.B F.shape N m n U), Opera.Price A.B F.shape N m n U K ∧
    (let P:=A.B.a.budget m; (∃ Yk:KLink P ((Beam.marquee K P).read (Song.plusone K (Match.staple (H:=K) (J:=K) rfl rfl rfl) Chi.canonical (A.B.kin.alpha N m)))
       (Time.forecastK A.B.a m F.scout U.beta/8) (P.supportExponent+1+1) P U'.activities (Time.quoteHard A.B.a m F.book U.beta) P.supportExponent,KLink.Last Yk))
include h g0 hW hm hk hh
lemma stepsT (hp:Appearance A Xξ X'.extra (m+1) n N k U) : (V).threshold^2* |βp-Mi| ≤ PostP.θ2 G s y k ∧ ∃ U', A.B.Move N m n U' U ∧ Appearance A Xξ Plead m n N k U' ∧ Costly A F m N n U' U:= by
 let p':= A.B.a; have hu:U.beta=β:=hp.beta; have hb:β∈ band p' (m+1):=((Xξ.sticks N n).prices (m+1) (by omega) hm).2; obtain ⟨V₂,w⟩:=hp.stamp; obtain ⟨K,hK⟩:= Opera.feature A.B F.shape hm F.pledging.conducts.full F.pledging.conducts.income hp.truep (show _ from hu.symm ▸ hb); have he:=PriceCompiler.beta_eq A.B.valid m; rw [he] at w
 let q:= βp-β-Γ; have hn:= actual_arch A F g0 hm Xξ hW hp.view; have hτ := quarterT R Q A F h g0 hm hk X' hh β hb hu hp.truep V₂ w K hK hn; rw [show β+Γ+(βp-β-Γ)=βp by ring] at hτ -- q let may rw
 obtain ⟨ht,u',ht',hLink,hB,Tz,hX⟩:= hτ; refine ⟨ht,u',ht',⟨hB,ht'.bundle,?_,Tz,hX⟩, K,hK,?_⟩
 ·
   rw [ht'.ident,hu,hp.view,(Xξ.moves N m n hm).ident]
 exact hu.symm ▸ hLink -- type of hLink? beta only rewriting R
end WheelP
end YM.AllOrder.Transit
