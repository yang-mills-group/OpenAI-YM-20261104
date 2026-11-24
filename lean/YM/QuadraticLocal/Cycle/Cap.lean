import YM.QuadraticLocal.Cycle.Pay
/-! # One supplier's numeric rates. Firm (installed after choosing stage) -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.MintClock
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
namespace Page
variable (G:Gauge)(D:Side)(P:Page)(U V:Stage)
variable (hP:Eligible G D P) (u:ℝ)
local notation "K"=> (fun x=> Pressure.betaF G x D)
local notation "Q"=> Delay.fineMonitor G D
local notation "D'"=> D.val
local notation "B"=> Pressure.radiusB
local notation "Bf"=> fun x=> Pressure.radiusB ( K x )
variable {ε:ℝ}(hε:0<ε)
local notation "Y"=> fun x:ℝ=> Page.reward (K x) ε
local notation "T"=> (Page.computes G D P)
local notation "W"=> (Page.temperature G D)
local notation "Ef"=> P.precision
local notation "MΦ"=> P.fidelity
open Footprint
-- Reserve polynomial budgets.Frame.Weight paid only on branches with height x.
lemma feesAround (f:ℝ)(hf:0<f)(a:ℝ)(ha:0≤a)(M:ℝ→ℕ) (h:Tendsto M atTop atTop) : ∀ᶠ x in atTop, Footprint.reserve f a ((M x:ℝ))⁻¹ (f/4):=by
    let g(x:ℝ):= (M x:ℝ); have ht:Tendsto g atTop atTop:= tendsto_natCast_atTop_atTop.comp h; have hh: Tendsto (fun x=> a*(g x)⁻¹) atTop (𝓝 0):= by simpa only [mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp ht).const_mul a
    filter_upwards [hh.eventually_le_const (show 0<f/2 from half_pos hf)] with x hx; exact ⟨ha,by linarith,by change a*(g x)⁻¹+_ ≤ _; linarith only [hx]⟩ -- lemma exists?
-- ledger on profile SAME.World.Shape.Region.Clock.Pixel
structure Firm (x μ : ℝ): Prop where
  cost : ∀ β:ℝ, inBand (Pressure.betaF G x D) β → ∀ p p', Page.enclosure U p (Pressure.radiusB (Pressure.betaF G x D)) (2*Pressure.fiery G x D) → Page.enclosure V p' (Pressure.radiusB x) (2*Pressure.fiery G x D) → Earnings.Cashier ( Page.computes G D P x ) G D p p' μ ( Willow.haloSlack ( Pressure.radiusB x )) (Coat.gStep β)
include hP hε
set_option maxHeartbeats 200000
lemma earns : ∀ᶠ x in atTop, Firm G D P U V x (Y x):= by
 let k:= P.precision; let ρ:= P.a/4; let σ:= P.b/4; let c:= U.supportExponent; let d:=V.supportExponent+1+1; let W' x:= Willow.haloSlack ( B x)
 have hc:0<c:= U.price_pos; have hd:0<d:=by unfold d; linarith only [V.price_pos]
 let A1:= Pressure.radiusB; let A2 x:= Pressure.radiusB (Pressure.betaF G x D)
 let hκ (f:ℝ→ℝ)(h:Reserve G D f):= tender G D hε f h
 filter_upwards [hκ _ (Page.tons G D P V), hκ _ (Page.proceeds G D P hP), hκ _ ( Reserve.const 4), hκ _ (Page.income G D P U Page.f_res c ρ), hκ _ (Page.income G D P V Reserve.field d σ), hκ _ (Reserve.const (Spire.fees D d)), hκ _ (Page.movement G D P V), hκ _ (Page.season G D),hκ _ hP.offered,hκ _ hP.swept, Page.morning hP, Work.E01.radiusB_tendsto.eventually_ge_atTop (2*Cable.links), (Work.E09.betaF_growth G D).eventually_ge_atTop 1, Page.town (G:=G) (D:=D), Page.feesAround P.a hP.lines.positive c hc.le A2 (Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth G D)),Page.feesAround P.b hP.lines.nonzero d hd.le A1 Work.E01.radiusB_tendsto, Access.wide (G:=G) (L:=D) (Rate.const (0:ℝ)), Page.mint_fail hP (P.precision-1) P.precision (by linarith only)] with x hnear hP' hΥ hIv hTv hz hv hy hX hE hA hx hk hh hρ hσ h hM
 constructor; intro β hb p p' hU hV; let g:=Coat.gStep β; let t:= (K x);
 let Bk:= Page.computes G D P x; have hp:0 < K x:= zero_lt_one.trans_le hk; obtain ⟨he,h'⟩:= h.2 β hb; have hw:1 ≤ W x:= (one_le_mul_of_one_le_of_one_le (by norm_num : (1:ℝ)≤ 4) (show 1≤ Delay.fineMonitor G D x from Real.one_le_exp (sq_nonneg _))); have hg:g≤1:=h'.le.trans (h.1.2.1.le.trans h.1.2.2.1.le); obtain ⟨ha,hB⟩:= hA β hb; obtain ⟨hm,hC,hH⟩:= Page.template G D P V x hV.1 -- check order.
 have hj:(Y x)>0:=by have hu:4≤Y x:= hΥ; linarith only [hu]
 refine ⟨hΥ,?_ ,?_ ,hP',?_,?_ ,?_ , (hP.height_p x).le,?_,hP.lines,⟨ha,(tuition hP x hk)⟩,?_,hE,hX,?_ ,?_ ,?_,?_⟩
 · change Invoice.price _ _ _ _ _ _ _≤_; rw [hU.1.2.2]; exact Eq.trans_le (Page.front_quote G D P U x hU.1 (A2 x) hU.2.1 c ρ) hIv
 · change Invoice.price _ _ _ _ _ _ _≤_; rw [hV.1.2.2]; exact Eq.trans_le (Page.front_quote G D P V x hV.1 (B x) hV.2.1 d σ) hTv
 ·  rw [hU.2.1]; exact hB
 · refine ⟨he,hg,hw,P.climate G D hP hp β hb _ hU.2.2,hP.lines.positive.le,?_⟩; rw [hU.2.1,hU.1.2.2]; exact hρ
 · refine ⟨he,hg,hw,P.climate G D hP hp β hb _ hV.2.2,hP.lines.nonzero.le,?_⟩; rw [hV.2.1,hV.1.2.2]; exact hσ
 · rw [hU.2.1,hV.2.1]; exact Page.frame G D P hP (B x) (Bf x) hh.1 hh.2.2 hx
 · unfold Earnings.lost; rw [hU.2.1]; exact (le_abs_self _).trans hM
 · rw [hm]; exact hnear
 · rw [hC]; exact hv
 · rw [hH]; exact hz
 apply le_of_eq_of_le (?_: (Y x)⁻¹=((Y x)⁻¹)) ?_; rfl
 exact (inv_anti₀ (inv_pos.mpr (Willow.spare_pos _)) hy).trans_eq (inv_inv _)
end Page
end YM.QuadraticLocal.MintClock
