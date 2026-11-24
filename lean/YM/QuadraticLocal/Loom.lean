import YM.AllOrder.Transit.Loom
import YM.QuadraticLocal.Lease
import YM.QuadraticLocal.Gaunt
import YM.QuadraticLocal.View
/-!
# One concrete trajectory walking re-expression receipt for marked use.

Use in the actual trajectory alongside Pass.These are explicit auxiliary lemmas
extending proofs of Transit/Loom: forecast extra halo slack (before exact r) from proposed
Frost extension and return a Walk of two Bills. Issued **before** any marked/tests in campaign.
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
local notation "Yz"=> Time.forecastE (a) m
local notation "Wz"=> Time.forecastK (a) m F.scout x
local notation "D₀"=> Time.fraction (a) m
local notation "D₁"=> Time.quoteHard (a) m F.book x
local notation "Ys"=> PostP.θ1 G s y k
local notation "Λ"=> (A.B.kin.path N m)
open UVNext.CouplingReset
open Progress.DirectedRecipe Ovens
local notation "B'"=> (p).clip
variable {q:ℝ} (hn:Ancillary A F x m n N U q)
local notation "βo"=> (x+Γ+q)
section outcome
-- from one query.F.E.Build.Summary.Delta.Origin.Lives.Proves with exact current beta.Anx. Witness.Out.
open Rosary
open PostP
local notation "θ"=> θ1 G s y k
local notation "M'"=>fun x':ℝ=>M0 k 0 V Plead x'
variable (hg:YM.QuadraticLocal.Beaming.Frost F.shape F.book F.scout A.delay)
include h hm hk hh hu hu' hx hp K hc g0 hn hg
local notation "χ₀"=> QuadraticLocal.Willow.haloSlack B
lemma budgeted : (V).threshold^2* |βo - Φ|≤ θ2 G s y k∧∃ U',A.B.Move N m n U' U∧ U'.beta=βo ∧ Nonempty (QuadraticLocal.Travel.Walk K U' (Wz / 8) Wz D₁ χ₀) ∧ ∃ C': Burn.Seed U' (M' βo), Candor (V) U'.activities (Set.range C'.model) (silver y) (young y k):= by
 obtain ⟨u⟩:= quoteF R Q A F h g0 hm hk X' hh x hx; let w:= (V); let v:= (Φ); let s':= s; let α:=Γ; let δ':=Φ-x-Γ; let b:= βo-Φ; let M₀:= M' v; let f':= y; have hX:0< f':= zero_lt_one.trans (A.B.a.fits.delayed m);
 have hτ := authentic_so R Q A F h hm hk X' hh x hx hu hp C₁ hu' K hc; have hT:U.path=A.B.kin.path N (m+1):= A.B.bases ▸ hp.path; obtain ⟨X₁,u',q',hQ,hS,E₁,Zℓ,⟨fτ⟩⟩:= first_class R Q A F h g0 hm hk X' hh π x hx K hc hu u C₁ hp.point hT (Shop.room_full A F h.formal.ladder) hτ
 let P := Λ; let a':= Δ0; obtain ⟨Lξ,v',ℓ,hY,hr,hV⟩:= hn.rents
 let S₁:= S★; have he:s'.clip=B':= congr_arg RG.Stage.clip (params_eq A.B.valid m).symm; obtain ⟨hz,hZ,H'⟩:= sameCost A (m:=m); let hi := low_tent R Q A F h hm π K; let κ := (vacant G (c!)); have h𝒦:κ.Ready V ((y) ^ (-(2/5:ℝ))):= pictures _ (by apply Real.rpow_nonneg hX.le);
 have h0(U':Config G (c!)) : gate Λ s X₁ u' w (offerS G V Plead (Age.scope (z+2)) (gStep (x+(v-x)))) κ (v-x) x q' U'=(S₁).push x U.eval U':= by unfold gate; rw [tsum_empty, Real.exp_zero,mul_one,show S₁=Y! from rfl,hS,show x+(v-x)=v from (by ring)]
 have hB: b = Averaging.delta (Lξ.read v')-δ':= by rw [← hr]; unfold b δ'; ring
 have hw: x+(v-x)+b=βo:= by unfold b v; ring
 obtain ⟨he0,ho,hb,hA,hJ,hb'⟩:= WheelP.mates R Q A F h hm hk X' hh x hx; have ht: |δ'|≤ a':= hb.trans (le_add_of_nonneg_right (Shop.cloak_gt D Y).le)
 let F' := F.book; let k' := Payments.Pairing.kGoal (F' Y E) t x; have hΓ : Payments.Rates (V).B D₁ Wz (y ^ (-(1/3:ℝ))) k':= by
    unfold Time.forecastK Time.quoteHard; rw [PriceCompiler.beta_eq A.B.valid]; exact (gleam R Q A F h).pays x (by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hx)
 have hτ': (s)=p:= (params_eq A.B.valid m).symm
 let p₁:=(p); have ha: x+(v-x)=v:=(by ring); have hB' : Width (pearl w) s'.clip s'.width:= (by change Width (pearl V) (s).clip (s).width; rw [hτ']; exact (bless R Q A F h hk).1)
 have hy': P.Bounds (s).clip (s).width (s).paths (A.B.a.clock.loopCap m):= by rw [hτ']; exact hi.1
 have hs':∀ U':Config G (c!),flags w.threshold U'=∅→ gate P s' X₁ u' w (offerS G w Plead (Age.scope (z+2)) (gStep (x+(v-x)))) κ (v-x) x q' U'=earlyValue Lξ P s'.clip w v' x ℓ (v-x-δ') U':= by
    intro U' _; rw [h0,show v-x-δ'=Γ by unfold v δ'; ring,he]; exact hV U'
 have hvK:Near y (x+(v-x)+b)∧ Near y (x+(v-x)) ∧ |v-x|≤ a'∧|δ'| ≤ a'∧ Yz≤y:= ⟨hw.symm ▸ hn.near,ha.symm ▸ ho,hA,ht,H'⟩
 have h𝒵 : Payments.Rates (V).B D₁ Wz (y ^ (-(1/3:ℝ))+χ₀) k':=by
    unfold Time.forecastK Time.quoteHard; rw [PriceCompiler.beta_eq A.B.valid]; let hξ:= hg.bears _ _ _ (step_paid A.B.a m) (A.B.valid.pays m); exact QuadraticLocal.Beaming.Leg.income hξ x (by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hx)
 obtain ⟨hD,V₁,K₁,h₁,⟨wZ⟩,T₁,hP,hP'⟩:= PostP.feast_ride s' (R.pre z E) (R.shape _|>.pos _) (wide R Q A F h) g0 (he.symm ▸ hi.2.2.2.2) hB' hy' y hX (zones R Q A F h|>.2.1) rfl rfl (LegalQ R Q A F h hk X' hh) ((bless R Q A F h hk).2.1) h𝒦 hQ hY hs' hB ((fitsB R Q A F h hk).post.solves) hΓ hvK (QuadraticLocal.Willow.spare_pos _).le h𝒵
 let μ:= Collection.vac u' q'; let U' := finish Λ s'.clip V V₁ K₁ (x+(v-x)+b) μ; have he': U'.eval=S₁.push x U.eval:= funext fun i=> (hP' i).trans (h0 i); have ht':U'=finish Λ B' V V₁ K₁ βo μ:= by unfold U'; rw [he,hw]
 refine ⟨hD,U',ht'.symm ▸ WheelP.advance A F g0 hm x hx hu hp hn V₁ K₁ (hZ.symm ▸ h₁) (ht' ▸ he'),hw,⟨E₁,Zℓ,X₁.read u',fτ,wZ⟩,?_⟩
 rw [← hw]; exact ⟨T₁,hP⟩
end outcome
end WheelP
end YM.AllOrder.Transit
