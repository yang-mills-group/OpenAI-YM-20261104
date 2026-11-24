import YM.LocalLTE.Concert.Snips
import YM.LocalLTE.Rendezvous.Plinth
import YM.LocalLTE.Rendezvous.Garden
/-!
# Compile additional analytic prerequisites. Uniform WAGES, no estimate left conditional. Measured AFTER Y shift on adjacency (hat). Doesn't take ancestry shots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
open LocalLTE.Inset Org
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open ClockB Urns
open LocalLTE.Fan LocalLTE.Fan.Pastel LocalLTE.Port LocalLTE.Port.LoopBank Coat
variable {G:Gauge}(L:Side)(p M:ℕ) {c L' d:ℝ}
-- W Φ.M. pre-force budget
variable (b m k:ℕ)(J μ ε:ℝ) -- length b, weight ≤β^μ, costs.
abbrev neat (x:ℝ)(z:ℝ):= x^(-z-2)
-- K-old boost bills for Photos.F.K reservation at prior MARK and radius consumed.True
local notation "Y0"=> Urns.divisor
-- Rating post constant. Shape p.Point.
variable (P:Stage)
local notation "M₀"=> m
-- no forcing equality needed in End passing `hv.eq` Y.K! set X.spherical intersection. Λ satisfying
variable (hc:0 ≤ J)(hm:0≤μ)(he: 0<ε)
local notation "p0"=> (slotPay G J b P.order P.power)
lemma budgetR {s':Side} {X:Rep G s'}(ht:J≥0) : 0≤ slotPay G J b X.p.order X.p.power:=by unfold slotPay; have hh:= G.colorScale_pos; positivity
include hc hm
lemma cope (r:ℝ) : ∀ᶠ x in atTop, let y:= Urns.divisor x; ∀ (B:BudgetPoint), B.order=P.order→B.power=P.power → B.supportExponent=P.supportExponent→ gross m b B (y^2) (x^μ* (slotPay G J b P.order P.power)) ≤ y*x^r := by -- parsing (y^2)
    let H:= Urns.divisor; let M:= slotPay G J b P.order P.power
    let K:= (m:ℝ)*Animals.ballCost (b+1); let f(x:ℝ):= K*H x^2
    have hK:0≤ K:=by unfold K; positivity
    let Q:=oneQ
    let A:=LoopBank.footprintCost b P.supportExponent
    let g(x:ℝ):=(1+A*(betaF G x Q ^ μ*M))^m
    have hg : Rate G Q (μ*m) g:=by
       unfold g; exact (((Rate.const (1:ℝ)).weaken hm).add (((Rate.power (a:=μ)).mul_right M).mul_left _)).pow _
    have hf:Rate G Q (-1) f:=by
        unfold f; apply Rate.mul_left; have hp:= (cheapest (G:=G) Q (-1)).pow 2; exact hp.weaken (by norm_num)
    let Y(x:ℝ):=2*K*H x*g x; have hh:Rate G Q (r-1) Y:=by
       unfold Y; convert! (((cheapest Q (r-1-μ*m)).mul_left (2*K)).mul hg) using 1; ring
    filter_upwards [hh r (by linarith only),hf.below (by norm_num) 1 ((show 0 < (1:ℝ) from zero_lt_one)), eventually_gt_atTop (0:ℝ)] with x h hv hx y P' hw hp hU -- tiny check
    let σ:=H x; have hs:=Urns.nonzero x; have ht:0 ≤ f x:= by unfold f; positivity
    have hy: f x ≤1:= (le_abs_self _).trans hv
    have hb:Real.exp (f x)-1 ≤ 2*f x:=by
       apply (le_abs_self _).trans ?_; simpa only [abs_of_nonneg ht] using Real.abs_exp_sub_one_le (show |f x| ≤ 1 from (abs_of_nonneg ht).trans_le hy)
    have hu: 0≤M:=by unfold M slotPay; have h₁:=G.colorScale_pos; positivity
    have hg: 0≤ g x:=by unfold g Q; rw [oneShift]; unfold A LoopBank.footprintCost; positivity
    change _ ≤ σ*_
    have hG:g x=(1+A*(x^μ*M))^m:=by unfold g Q; rw [oneShift]
    change Real.exp _-1 ≤ _ at hb
    unfold gross LoopBank.footprintCost; rw [hU]; change fog m b (H x^2)*(1+A*(x^μ*M))^m ≤ _; rw [← hG]; refine ((mul_le_mul_of_nonneg_right hb hg).trans_eq (show 2*f x*g x=σ*Y x from ?_)).trans (mul_le_mul_of_nonneg_left ?_ hs.le)
    · unfold Y σ f; ring
    have hX : |Y x|≤_:= h; rw [oneShift] at hX; exact (le_abs_self _).trans hX
-- footprint budgets α.standing. P¹ uses P model price. Port.turn. ν chosen. keep T.M.Sum.Root.
-- earlier Yμ.O. one weight vector r=neat. proof occupancy forecast.H.W.Is.
local notation "A₀"=> LoopBank.footprintCost b P.supportExponent
local notation "A'"=> LoopBank.sonic b P.power P.order
local notation "W" x=> (neat x μ)
local notation "K₀" x=> (x^μ)
local notation "V₀" x=> (x^(-ε))
def phaseT (M:ℝ)(x:ℝ):=(m:ℝ)*((neat x μ)*(A₀*((x^μ)*A'*M))) -- remove z
-- event βF shift needed for angle.D vector in Turn.C.G.dist upper. scales.
local notation "U" x=> (L.val*radiusB x)
variable {K:ℝ} (i:ℕ) (hi:ε<(i:ℝ)/4)
omit hm hc in
lemma cheapT (Z:ℝ)(s:ℝ→ℝ) (h:Rate G L Z s): Rate G L (Z-2) (fun x=>phaseT b m μ P (s x) (betaF G x L)):=by
   unfold phaseT
   convert! Rate.mul_left -- order edit
            ((Rate.power (G:=G) (L:=L) (a:=-μ-2)).mul (((((Rate.power (a:=μ)).mul_right A').mul h)).mul_left _)) (m:ℝ) using 1 ; ring
include he
omit he hm hc in -- no need?
lemma afterShift (r:ℝ): Rate G L r (fun x=>Urns.divisor (betaF G x L)):=by
   intro s hs; filter_upwards [(Work.E09.betaF_growth G L).eventually (Mallow.cheapest (G:=G) oneQ r s hs)] with x hx; rwa [oneShift] at hx
-- semantic.W height foo.All relative M.(k). assumes casts valuations.S(costAP).

omit hm in
lemma summerB : ∀ᶠ x in atTop, let t:= betaF G x L; let q:= Urns.divisor t; let s:= K₀ t; let z:= t^(-ε); let r:= neat t μ; ∀ V:Type,∀ [Fintype V], Fintype.card V ≤ k →∀ (P':BudgetPoint),P'.order=P.order →P'.power=P.power → P'.supportExponent=P.supportExponent → capacity P' V (LoopBank.costAP m r P' b (p0+z) s) (LoopBank.costAP m r P' b z s) q z (t^ε) (U x) ≤ t^(-(1:ℝ)):=by
    let Z x:= betaF G x L; let D:=Urns.divisor; let Q:=oneQ; let f(x:ℝ):=(radiusB x)
    let u x:= (p0+ V₀ (Z x)); let w x:= (U x); let F(x:ℝ):=(1+(w x:ℝ))^(P.power*P.order)
    have hh : Rate G L 0 (fun x=>(w x:ℝ)):=by unfold w; simp_rw [Nat.cast_mul]; exact Rate.radius_price.mul_left _ -- radiusB Rate.const syntax
    have ht : Rate G L 0 F:=by simpa only [zero_mul] using! (((Rate.const 1).add hh).pow (P.power*P.order))
    let R x:=phaseT b m μ P (u x) (Z x)
    have hf: Rate G L (-2) R:= by have h':Rate G L 0 u:= (Rate.const _).add (Rate.power.weaken (by linarith only [he])); have hp:=Mallow.cheapT L b m μ P (G:=G) _ _ h'; simpa only [zero_sub] using! hp -- check
    let T x:=phaseT b m μ P (V₀ (Z x)) (Z x)
    have hT:Rate G L (-ε-2) T:= by unfold T; exact cheapT L _ _ _ _ _ _ Rate.power
    let Axx (x:ℝ):=2*(F x*((k:ℝ)*R x)) +(Z x)^ε*(2*(k*T x)+2*((k:ℝ)*((Z x)^(-ε)*(D (Z x))))) -- parentheses verify
    have ha: Rate G L (-2) Axx:= by
       let g':ℝ→ℝ:=fun x=> (V₀ (Z x))*(D (Z x)); have hg:Rate G L (-ε-2) g':=by unfold g'; simpa only [sub_eq_add_neg] using! ((Rate.power (a:=-ε)).mul (afterShift L (G:=G) (-2))) -- order
       refine Rate.add ?_ ?_
       · simpa only [zero_add] using! (ht.mul (hf.mul_left k)|>.mul_left 2)
       convert! ((Rate.power (G:=G) (L:=L) (a:=ε)).mul (((hT.mul_left k).mul_left 2).add ((hg.mul_left k).mul_left 2))) using 1; ring
    filter_upwards [ha (-1) (by norm_num), Work.E09.betaF_growth G L|>.eventually_ge_atTop 1] with x hx hp t q z s r V H hv P' h hS hE
    refine le_trans ?_ ((le_abs_self (Axx x)).trans hx)
    have hz:0< Z x:= zero_lt_one.trans_le hp; let J':=Fintype.card V; have hj:(J':ℝ) ≤ k:=by exact_mod_cast hv
    have hG:0≤(Z x)^μ:=Real.rpow_nonneg hz.le _; have h₀:0≤ (V₀ (Z x)) := Real.rpow_nonneg hz.le _; have hv:0≤ u x:=add_nonneg (by unfold slotPay; have hh:= G.colorScale_pos; positivity) h₀
    have hh1(s:ℝ)(hs:0 ≤ s):0 ≤ phaseT b m μ P s (Z x):= by
        unfold phaseT neat; have hf:= LoopBank.sunny b P.power P.order; have hw:0≤ LoopBank.footprintCost b P.supportExponent := Real.exp_nonneg _; positivity
    unfold Axx capacity turnQ costAP LoopBank.payment LoopBank.sonic LoopBank.footprintCost -- port unknown.
    rw [h,hS,hE]
    change 2*(F x*(J'*R x)) +(Z x)^ε*(2*(J'*T x)+2*(J'*(s*q))) ≤ _
    have hi:0 ≤ F x:=by unfold F; positivity
    exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj (hh1 _ hv)) hi) zero_le_two) (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj (hh1 _ h₀)) zero_le_two) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj (mul_nonneg h₀ (Urns.nonzero _).le)) zero_le_two)) (Real.rpow_nonneg hz.le _)) -- t parentheses.T.check order
end YM.PhysicalNext.Repeat.Mallow
