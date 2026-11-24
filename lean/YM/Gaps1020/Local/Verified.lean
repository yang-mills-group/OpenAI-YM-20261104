import YM.Gaps1020.Local.Invoice
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
local notation "ℓ₀" => turnFee P₀
local notation "Δ" => ℓ₀ * ((Z^(M+1))⁻¹)
local notation "d'"=> H.ordinal
local notation "V'" i=> Rain.moor R.target A m i
local notation "Z0"=> screens R.target A m
local notation "wid"=> Rain.lint R.target A m
local notation "e"=> Trio.base wid (radiusB x₀)

set_option quotPrecheck false
local notation "pX"=>opening W
local notation "F'"=>Magazine E0→ Config G C0→ℝ
local notation "hg1"=> (plusone E0 X0 O φ).hardRead
local notation "P'"=> Beam.marquee E0 P₀
local notation "k1" => (Cash.armK (R.target i0 j0) L0 (R.shape.μ i0 j0) x₀ 0 (R.expense i0 j0).degrees)
local notation "k0" => (forecastK A.B.a m R.scout (Y x.val).beta)

local notation "p0" => quota A m M
local notation "p1" => demand A wid m p0
local notation "P₁"=> A.B.kin.path N m
local notation "v1"=> H.result x
local notation "V1"=> (v1).activities
local notation "Φ" a:max => Averaging.delta ((pX).read a)
local notation "Ψ" I:max x:max => coverWorld V1 pX P₀ P₁ (A.B.a.params m).clip I x
local notation "Y0"=> A.B.a.clock.allowance m
local notation "D'"=> A.B.a.clock.forcedAllowance m

-- β and v approximants read BEFORE installing; evaluation identity separate
-- includes exact unaltered β,scalar when claiming denominator. Optionally
-- use projections if paying curvature matrix separately! Support and mask
-- agreement strong through actual finish. `Local` output after renumbering,
-- paid residual includes Mat/Core.affine Hessians etc, all sectors push.
-- β error in raw beta, no scaled Jacobian applied. Keeps χ common. Valid
-- and E/K norms, not Hits persistence under next trajectory.
variable (M) (hG:G.Simple)
local notation "G₀" => proposed M H x
local notation "G₁" => ignored M H x
local notation "p₀" => (H.result x.val).p
local notation "R'" => H.result x.val
local notation "H0"=> (√(2:ℝ) * Vacuum.nativeG (V₀).beta)
-- projection algebra. At post actual β & scalar may then be rewritten as βApprox+Δr etc.
section repair
-- exact split of full posterior E exponent including tests. priced at SAME
-- representations (EBound,KBound) rather than tally gauge.
lemma summedRepair {E F R: Activities G c}{P:BudgetPoint}{l m n:ℝ}(hl:R.E=E.E+F.E)(hE:E.reg=R.reg)(hF:F.reg=R.reg)(he:E.Valid P l n)(hf:F.Valid P m n): R.additive P=E.additive P+F.additive P:=by
   funext U; unfold Activities.additive; rw [Pi.add_apply, ← Summable.tsum_add (f:=fun i=>E.regularOccurrence P i U) (g:=fun i=>F.regularOccurrence P i U)]; apply tsum_congr; intro i; unfold Activities.regularOccurrence; rw [hl,hE,hF]; by_cases h:Healthy P.threshold (R.reg i).support U; all_goals try simp [h,masked]; -- robust
   exact (Activities.ESeries he).summable U
   exact (Activities.ESeries hf).summable U
private lemma deliversP (R:RG.Rep G c)(F E:Activities G c)(Q:RG.Rep G c)(h: Q={R with activities:=F})(a:ℝ)(hf:F.Valid R.p a s)(he:E.Valid R.p l s)(hE:E.reg=R.activities.reg)(hF:F.reg= R.activities.reg)(hK:F.K=R.activities.K)(ht:F.forced=R.activities.forced)(hV:R.activities.E=F.E+E.E)(U:Config G c): R.eval U=Q.eval U * Real.exp (-(E.additive R.p U)):=by
   subst Q; unfold RG.Rep.eval RG.Rep.exponent; dsimp only; have hg: F.gas R.p U=R.activities.gas R.p U:=by unfold Activities.gas Activities.gasOccurrence Activities.admissible; rw [hK,ht]
   rw [hg, summedRepair hV hF hE hf he, Pi.add_apply, show R.v* Fintype.card (Site c) - R.path.inChannels R.clip R.p R.beta U - (F.additive R.p U+E.additive R.p U)= _ from (show _= R.v* Fintype.card (Site c) - R.path.inChannels R.clip R.p R.beta U - F.additive R.p U + (-(E.additive R.p U)) from sub_add_eq_sub_sub .. |>.trans (sub_eq_add_neg ..)), Real.exp_add]; ring
end repair
-- avoid macro binder. exact identity in `Rep` shape including Masked E & Gas incidence, behind same α,τ.
local notation "X!"=> (H.result x.val).activities
def presentation : RG.Rep G C0 := {H.result x with activities:=proposed M H x}
structure Posterior (p: ℝ):Prop where
   fit : (G₀).Valid P₀ (Y0+p) D'
   cut : (G₁).Valid P₀ p D'
   volume : (P₀)=p₀
   exacts : (X!).E=(G₀).E+(G₁).E
   matters (U:Config G C0) : (R').eval U=(presentation M H x).eval U *Real.exp (-(G₁).additive P₀ U)
   coupling : |(R').beta-betaLow M H x| ≤ p
   scalar : |(R').v -scalarPlan M H x| ≤ p
include h he hM hG
lemma presentB (hC: Mallow.RG12.Earned (checkout G) R.shape A.delay)(hx:M=Renew.premium d): Posterior (M:=M) H x ((H0)^(d+1)):=by
   obtain ⟨hk,ht,hq,hδ,hF⟩:= adapt M H x h he hM hG
   obtain ⟨ha,hv,hp⟩:= bank H x h he hM hC hx
   refine ⟨⟨hk.regular,hk.forced,hk.moves,Time.E_rises hk.boundE (add_le_add_right ha Y0),hk.boundK⟩,⟨ht.regular,ht.forced,ht.moves,Time.E_rises ht.boundE ha,ht.boundK⟩,rfl,hq,?_,?_,(priceScalar M H x h he hM hG).trans hv⟩
   · exact fun U=> deliversP R' G₀ G₁ _ rfl _ hk ht (by unfold ignored coverWorld; rfl) (by unfold proposed coverWorld; rfl) (by unfold proposed coverWorld; rfl) (by unfold proposed coverWorld; rfl) hq U
   rw [hδ, add_sub_cancel_left]; refine le_trans ((le_div_iff₀ ((sq_pos_of_pos (P₀).threshold_pos))).2 ?_) hp; exact (mul_comm ..).trans_le hF
end YM.GapsLocal.Renew
