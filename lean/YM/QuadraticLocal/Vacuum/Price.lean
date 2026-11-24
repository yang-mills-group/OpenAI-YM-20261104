import YM.AllOrder.Transit.Conditions
import YM.QuadraticLocal.Vacuum.Lift
/-!
# General E with the same Lease for the mixed step too

 See Transit.Conditions; the sale is now relative.
-/
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
-- As in RG03/Battle/Sail. Replace only `A.B`'s history-based retain test by
-- True, leaving all prices, paths and bands in force. This is used to instantiate
-- the Markov component procurement proof, not an alternative construction used after
-- the fact to select weights.
@[reducible] def neutral {G:Gauge}{X:Metals G}{D:Rolls X.p}(A:Alloy X D) := {A.B with bake:= { A.B.bake with path:=A.B.kin.path, retain:= fun _ _ _ _=>True}, bases:=rfl}
variable {U: RG.Rep G (A.B.a.S.side (m+1) n)} (hu:U.beta=x)
    (hp:Lives (neutral A).bake N (m+1) n U) (C₁:Burn.Seed U (M0 k 0 (A.B.a.budget (m+1)) (X'.extra) x))
    {e:ℝ}(hé:e ≤ High.serving (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))))
    (hu':Candor (A.B.a.budget (m+1)) U.activities (Set.range C₁.model) (silver (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1))))) e)
    (K:Guide A.B F.shape N m n U)(hc:Opera.Price A.B F.shape N m n U K)
local notation "M"=> Set.range C₁.model
local notation "h′"=> LinkPat A F π K k M
local notation "Γ"=> A.B.kin.alpha N m
local notation "Θ"=> poem R A F X' π x K C₁
local notation "Op"=> Chi.canonical
local notation "v★"=> (heap G s (1/16)*young t k)
local notation "V₀"=> 2*v★
abbrev Certified : Prop:= Lock F.shape F.v F.prices F.t F.span F.recordP (wind F.menu) A.delay
variable (Ψ: Certified A F)
local notation "w"=> F.v Y E
local notation "Zj"=> caloric G y L k e
local notation "δq"=> attenuation t
local notation "W₀"=> (F.v Y E / ((D.L (A.B.a.clock.J (m+1))).val:ℝ))
local notation "Lξ"=> (F.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.earn)
local notation "R0:" => tiredT K (Burn.typeT M k) (alt k)

include hk hé Ψ hu' hp hm
lemma rewardW : ∃ (c d v t' a₀ b r m₁ q : ℝ)(l:ℕ)(N:Captain K (X.p.profile E).order c d v t' a₀ b r m₁ q l Op), Ac.Hit (Captain.reachability (H:=K)) (radiusB (A.B.a.clock.hatBeta m)) (fun z' => if R0: z' then N.markΦ z' ((X.p.profile E).power) else 0) Lξ Zj:= by
 have hx₀:= Ψ.actor _ _ _ (A.B.valid.pays m) (step_paid A.B.a m); have hk0:k≤E:= by unfold Burn.horizon at hk; omega

 exact (hx₀.opens k hk0).1.renew (A.B.a.S.side m n) (A.B.a.S.side (m+1) n) (Pane.panel A m π) (Pane.orchestra A N π) K.laws.data.funds (ovation A N π hm F.pledging.conducts.full) U K (Set.range C₁.model) e (hp.point.symm ▸ hu') hé

variable {c d v T₁ a₀ b r m₁ q' : ℝ}{l:ℕ}(K': Captain K ((X.p.profile (A.B.a.clock.J m)).order) c d v T₁ a₀ b r m₁ q' l Chi.canonical)
include hm h hc hk hé Ψ hu hu' hx hp hh K'
set_option maxHeartbeats 300000 in
lemma reward_individual : haze (k:=k) (Mξ:=M) A F π K (W₀*e+δq*e):= by
 have hx₀:= Ψ.actor _ _ _ (A.B.valid.pays m) (step_paid A.B.a m); have hk0:k≤E:= by unfold Burn.horizon at hk; omega

 let δB:=e
 let S₀:= S★; let u:= F.pledging.conducts; have hi:= step_paid (a) m; let v :ℝ:= F.span Y E; let desk := assigned u.hearing.plan m n A.B N U
 have ho:= (Psalm.Stage.directed u.hearing (neutral A) hm (hu ▸ hx) hp (fun m' h' => u.full _ _ _ (by simp at h'; omega))).1.enabled
 have hf:= ho.make; obtain ⟨hA,hc'⟩:= ho.pre; have hℓ:= (ho.clocks U.beta (hu ▸ hx)).2; rw [← hp.point] at hf hA hc' hℓ; obtain ⟨hz',ht,hr⟩:= F.pledging.agenda _ _ hi; have ht':preExponent V= (s).supportExponent+3:= congr_arg (fun t':RG.Stage=>t'.supportExponent+3) (params_eq A.B.valid m)
 have hX: g=L:= PriceCompiler.block_eq A.B.valid m; let P':= V; let U':= F.menu; have hv':(T).halo+5 ≤ F.span Y E:=hr; have hV := K.laws.data.room.sight; -- not needed
 have he:P'.power= (s).power:= (zones R Q A F h).2.1.1
 have hp' : Candor U.p U.activities M (silver t) δB:= hp.point.symm ▸ hu';
 let eL:= F.recordP Y E
 have he : Brim.Homes M K eL desk.broadCut desk.profile Op desk.radius P' (Solo.raise F.t Y E) (W₀*δB) (δq*δB):= (hx₀.oldE (first_le A.B.valid m)).stays _ _ S₀ (ships A.B N m n) K.laws.data.funds U _ _ K P' rfl he hf hr (hX ▸ hA) (he ▸ hc') (hX ▸ hℓ) _ le_rfl _ _ _ _ _ _ _ _ _ _ K' desk.broadCut desk.radius M (silver t) δB hp' (budget_nonneg (hp'.sale.choose_spec.2 0|>.2)) (hé.trans (hx₀.opens _ hk0).1.eligible)
 have hz:haze (k:=k) (Mξ:=M) A F π K (W₀*δB+δq*δB):= by exact Height.icon_budget V Op rfl he (ht'.trans_le (ht.trans (le_add_of_nonneg_right zero_le_two)))
 exact hz
omit K'
set_option maxHeartbeats 400000 in
lemma sale_so : ∀ᶠ t' in atTop,Meadow.Budget V (Beam.marquee K V).reg (linger (Θ t') Op t' Φ (Φ-x)).logRead (away s*((Zj+(W₀*e+δq*e))+pen G L k y 0)+pen G L k y 0):=by
 obtain ⟨C',d',v,u',z',b',r',B',q,l,K',hK⟩:= rewardW R A F hm hk X' x hp C₁ hé hu' K Ψ
 exact shiningW R Q A F h hm hk X' hh π x hx K hc hu hp.point C₁ K' hK (reward_individual R Q A F h hm hk X' hh x hx hu hp C₁ hé hu' K hc Ψ K')
end WheelP
end YM.AllOrder.Transit
