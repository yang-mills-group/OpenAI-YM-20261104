import YM.QuadraticLocal.Normalization.Bank
import YM.QuadraticLocal.Loom
/-!
# Virtual β-payment soft costs

Reuses Frost & PostP.Checks from `WheelP.budgeted` without consuming Real Paths `Move`.
Benchmark issued for the GENERAL E comparison too (preReset). NO positivity assumption on P.eval.
Monotonicity arguments for grams reusing proof of
`YM/IterationFrontier/Larch/Aspen/Invited`.
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
variable (Ψ: Certified A F)
local notation "w"=> F.v Y E
local notation "Zj"=> caloric G y L k e
local notation "δq"=> attenuation t
local notation "W₀"=> (F.v Y E / ((D.L (A.B.a.clock.J (m+1))).val:ℝ))

local notation "M0o"=> ( M0 k 0 V (Plead) (Φ) )
local notation "Ws"=> ( Time.forecastK (a) m F.scout x )
local notation "Λ"=> (A.B.kin.path N m)

variable (F₁: Tree.Forest (Pane.panel A m ((A.B.a.S.oneStep m n).exact_size)).ratio)
open QuadraticLocal
-- zℓ = extra soft marker assemblybudget currency. b₁ output hard warrant(via Gates next).
variable (L₁:Listing G (A.B.a.S.side m n))(Z:Collection.Source G (A.B.a.S.side m n))(ℓ₀ Hc:ℝ)(hKx: Arrival R Q A F hk X' x K F₁ L₁ Z ℓ₀ Hc)
open Rosary
local notation "Y₁"=> (PostP.C' V G k Φ y)
local notation "α"=> (Φ-x)
local notation "D₁"=> Rosary.Guard.Dusk.shipment Λ (s).clip V L₁ Z M0o x α ℓ₀
-- bind theory to explicit compiler clocks, at current η & layout. use notation in conclusion not h variables
variable (zℓ yℓ W₁ :ℝ)

section gram
open UVNext.PricedKernels Ovens
private lemma affine (p₀ : BudgetPoint) (Su : RG.Stage) (α₀ H : ℝ) :
    softNeed G p₀ Su.clip Su.width Su.paths α₀ H = softNeed G p₀ Su.clip Su.width Su.paths α₀ 0 + softNeed G p₀ Su.clip Su.width Su.paths 0 1 * H := by
   unfold softNeed hitNeed softReset Footprint.payment Footprint.degreeIncome; rw [abs_zero]; ring
lemma soft_nn (p₀ : BudgetPoint) (Su : RG.Stage) {H : ℝ} (α₀ : ℝ) (he:0≤ H) : 0 ≤ softNeed G p₀ Su.clip Su.width Su.paths α₀ H := by
   have hu:=VerifiedReset.Residual.loss_pos G p₀; have hf:=pair_nonneg G p₀; have hp:= (Collection.budget_pos p₀ G Su.clip Su.width_pos Su.paths_pos.le).2.2
   have hv: 0 ≤ (1-Real.exp (-1))⁻¹:= inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))
   unfold softNeed softReset hitNeed Push.AbsoluteSums.Footprint.payment Push.AbsoluteSums.Footprint.degreeIncome
   have hi :=p₀.threshold_pos; positivity

end gram


open UVNext.CouplingReset UVNext.PricedKernels Ovens
open Rosary.Repair.PostP Progress.DirectedRecipe Ovens
local notation "Wₓ"=> (Time.quoteHard (a) m F.book x)
local notation "Wℓ"=> (QuadraticLocal.Willow.haloSlack B)

variable (hg:YM.QuadraticLocal.Beaming.Frost F.shape F.book F.scout A.delay)
include hm h hh hx hk g0 hg hKx
set_option maxHeartbeats 600000 in
lemma compensated : Benchmark R Q A F hk X' x K F₁ L₁ Z ℓ₀ Hc Wℓ Wₓ := by
 let s':=(s); let hP:=hKx.licensed; have hs : (s)=p:= (params_eq A.B.valid m).symm
 obtain ⟨hρ,hη⟩:= wide R Q A F h (n:=n) (m:=m);
 obtain ⟨hX,hX0,hw⟩:= paint R Q A F h g0 hm hk X' hh x hx (show 4≤ (c!).val from (by omega));
 have hwL:= ( low_tent R Q A F h hm π K ); have hv: (Λ).Bounds (s).clip (s).width (s).paths (A.B.a.clock.loopCap m):=hs.symm ▸ hwL.1
 have hV:Width ( Rosary.pearl V ) (s).clip (s).width:= hs.symm ▸ (bless R Q A F h hk).1
 let yV:= (V); have hc : WilsonStartup.Decent (s).clip V:= hs.symm ▸ hwL.2.2.2.2
 let ζ' := y; let u:= (Φ); let t' := θ1 G s' ζ' k; have hζ:0<ζ':= zero_lt_one.trans (A.B.a.fits.delayed m)
 have hθ:0 ≤ t' := mul_nonneg (Time.credit_pos G s').le (Real.rpow_nonneg hζ.le _)
 have hsK:= Guard.Dusk.supports hP.paid
 have hK:Collection.Local L₁ V ( Rosary.Guard.Dusk.nothing Z ) t' Ws:= by
    obtain ⟨z',hv,hX⟩:=hsK.cheap; exact {hsK with cheap:=⟨z',hv,fun x₁=>budget_loosen (hX x₁) hθ⟩}
 have hU:= Guard.future hv hc hV hη g0 0 α M0o hX hX0 hK; let Yx:= PostP.C' V G k Φ ζ'; let k' := Payments.Pairing.kGoal (F.book Y E) t x
 have hΩ :0 ≤ Guard.totalFee (V) G s'.clip s'.width s'.paths α 0 Yx t':= by exact hU.1.H_nonneg
 obtain ⟨he0,ho,hb,hA,hJ,hb'⟩:= WheelP.mates R Q A F h hm hk X' hh x hx; have ht : |(0:ℝ)| ≤ Δ0:= by rw [abs_zero]; linarith only [hA,abs_nonneg (α)] -- abs α syntax
 let u' : PostP.Actor G s' k (Δ0) (ζ') := ⟨V,⟨zones R Q A F h|>.2.1,rfl,rfl⟩,c!,⟨hρ,hη⟩,u,u,α,0,0,0,0,⟨ho,ho,hA,ht,le_rfl,hζ.le⟩, (by rw [sub_self, sub_zero]), (by rw [abs_zero,mul_zero]; exact hθ),(by rw [abs_zero,add_zero]; apply mul_nonneg (Gyro.rev (V) _); exact mul_nonneg hΩ (Real.exp_nonneg _)) ⟩
 let Γ':= (fun k₀:ℝ=> softNeed G V (s).clip (s).width (s).paths α k₀ ); let κ:ℝ:= (s).clip.direct; have h0:= ( (fitsB R Q A F h hk).post.solves u').kernel
 obtain ⟨Lℓ⟩:= Lapis.Signal.in_time ( c! ) hη yV; let hZ:= ((Lapis.go Lℓ 0 g0 hc.radius).2)
 obtain ⟨u₁,H',hθ'⟩:= hZ.2.2; have h₀: 0≤ Lapis.flare G (c!) yV 0 := budget_nonneg (hθ' 0)
 have h₁: Γ' 0 ≤ ζ'^ (-(1/3):ℝ):= by
    change Lapis.flare G (c!) yV 0 + (ζ'^(-(2/5:ℝ))+ Γ' (2*t')) ≤ _ at h0
    have hh : Γ' 0 ≤ Γ' (2*t'):= by unfold Γ'; rw [affine (G:=G) yV s' α (2*t')]; exact le_add_of_nonneg_right (mul_nonneg (soft_nn yV s' _ zero_le_one) (by positivity))
    linarith only [h0,h₀, Real.rpow_nonneg hζ.le (-(2/5:ℝ)), hh] -- coe issues?
 have hΓ : Payments.Rates (V).B Wₓ Ws ((y) ^ (-(1/3:ℝ))) k':= by
    unfold Time.forecastK Time.quoteHard; rw [PriceCompiler.beta_eq A.B.valid]; exact (gleam R Q A F h).pays x (by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hx)
 have h𝒵 : Payments.Rates (V).B Wₓ Ws (y ^ (-(1/3:ℝ))+Wℓ) k':=by
    unfold Time.forecastK Time.quoteHard; rw [PriceCompiler.beta_eq A.B.valid]; let hξ:= hg.bears _ _ _ (step_paid A.B.a m) (A.B.valid.pays m); exact QuadraticLocal.Beaming.Leg.income hξ x (by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hx)
 have hΓ₁:0≤Γ' 0:=soft_nn (V) (s') _ le_rfl
 exact logTrace R Q A F h g0 hm hk X' hh x hx K F₁ L₁ Z ℓ₀ Hc hKx Wℓ k' Wₓ (hedge_ok hΓ hΓ.hard le_rfl hΓ₁ h₁ le_rfl) (hedge_ok h𝒵 hΓ.hard le_rfl (add_nonneg hΓ₁ (QuadraticLocal.Willow.spare_pos _).le) (add_le_add h₁ le_rfl) le_rfl)
end WheelP
end YM.AllOrder.Transit
