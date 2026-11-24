import YM.QuadraticLocal.Cycle.Page
import YM.Extra.ITERATION_NO_LOSS.Rebuild
/-! # Size conversions payable simultaneously with Roll_Ψ clock. Uniform stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.MintClock
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
namespace Page
variable {G:Gauge}{D:Side}{P:Page}{u t b:ℝ}{M:ℝ→ℕ}
local notation "K"=> fun x=> Pressure.betaF G x D
local notation "Q"=> Delay.fineMonitor G D
local notation "D'"=> D.val
local notation "F"=> Pressure.radiusB u
local notation "Bf" => fun x=>Pressure.radiusB (Pressure.betaF G x D)
variable (hP:Eligible G D P)
lemma town : ∀ᶠ x in atTop, 1≤ radiusB x ∧ radiusB x ≤ Pressure.radiusB (betaF G x D) ∧ Pressure.radiusB (betaF G x D) ≤ 2*radiusB x:=by
 filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ), (Extra.Iteration.Rebuild.geometry (G.slopeConstant*Real.log D.val))] with x hx he h
 refine ⟨hx, ?_,h.1.1⟩; unfold radiusB; gcongr <;> first | exact Real.log_nonneg he.le | exact zero_lt_one.trans he | exact le_add_of_nonneg_right (Work.E04.shift_nonneg G D)
lemma f_res : Reserve G D (fun x=>(Pressure.radiusB (betaF G x D):ℝ)):=by
 refine (Reserve.mul (Reserve.const 2) Reserve.field).compare ?_; filter_upwards [(town (G:=G) (D:=D))] with x h; rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact le_trans (show _ ≤ 2 * (radiusB x:ℝ) by exact_mod_cast (h.2.2 : Bf x ≤ _)) (le_abs_self _)
lemma hcap : Reserve G D (fun x:ℝ=> (P.helm (radiusB x):ℝ)):=by
 apply (Reserve.mul (Reserve.const (Trio.maxFixed P.occupancy:ℝ)) Reserve.field).compare; filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx; rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact le_trans (show (P.helm (radiusB x):ℝ) ≤ (Trio.maxFixed P.occupancy:ℝ)* (radiusB x:ℝ) from (by exact_mod_cast P.roof _ hx)) (le_abs_self _)
lemma topReserve : Reserve G D (fun x:ℝ=> ((P.span (radiusB x)):ℝ)):=by unfold Page.span Radii.survey; push_cast; exact (Reserve.const _).mul Reserve.field
lemma expired (m:ℝ→ℕ)(u:ℝ)(hu:0<u) (v:ℝ)(hh:∀ᶠ x in atTop,radiusB x≤ m x): Rate G D v (fun x=> Real.exp (-u*(m x:ℝ))):=by
 apply (Rate.cutoff (G:=G) (L:=D) (a:=v) hu).compare; filter_upwards [hh] with x hx; rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hu.le); exact_mod_cast (Nat.le_trans ( Nat.div_le_self ..) hx: Pressure.Stores.till x ≤ m x)
include hP
local notation "w"=> P.computes G D u
abbrev missed (G:Gauge) (D:Side) (P:Page) (x:ℝ):ℝ:= Width.mint D P.cap P.order P.c P.b * Width.flat P.c P.a (P.height x) ( Pressure.radiusB (betaF G x D)) (P.span (radiusB x)) -- local macro Hygiene G D from old variables! avoid
lemma mint_fail (k:ℝ): Rate G D k (Page.missed G D P):=by
 let Y x:=P.height x; let a:=P.c; let b:=P.a; let F₀:= (hP.paid); have he':0<a:= hP.lines.waist
 let T x:= Pressure.radiusB (K x); have hT:(∀ᶠ x in atTop,radiusB x≤ T x):=(town (G:=G) (D:=D)).mono fun x hx=> hx.2.1;
 have hx₁ := (expired (G:=G) (D:=D) T (a-a/2) (by linarith) k hT).mul ((Rate.const (1:ℝ)).add hP.paid.rate)
 have hz:0<b:= hP.lines.positive; have hY:∀ x,radiusB x≤ P.span (radiusB x):= fun x=> le_trans (b:=5*radiusB x) (by omega) (Mentor.Radii.first ..)
 have hx₂ := (( expired (G:=G) (D:=D) T (b/2) (by linarith) k hT).add ( expired (G:=G) (D:=D) (fun x=> P.span (radiusB x)) (a/8) (by linarith) k (Eventually.of_forall hY))).mul (hP.paid.rate)
 simp only [add_zero] at hx₁ hx₂; exact (hx₁.add hx₂).mul_left _
lemma tuition (x:ℝ)(hx:1≤Pressure.betaF G x D) : P.fidelity G D x ≤1:= by
 apply Real.rpow_le_one_of_one_le_of_nonpos hx; unfold Tuition.need AllOrder.Catch.graded; push_cast; linarith only [hP.sound,Nat.cast_nonneg P.order (α:=ℝ)]
-- cliff birth vs stage.Cert formula.Actor_Core.Geometry.Payload.Type
lemma morning : ∀ᶠ x:ℝ in atTop, ∀ β,inBand (Pressure.betaF G x D) β→(gStep β)^P.depth ≤ P.fidelity G D x ∧ Real.exp (-(P.a/4))^ (Bf x) ≤ (gStep β)^P.depth := by
 have ht:P.precision>-(1/2:ℝ)*P.depth:= by
       have hx: ↑(P.order+1)≤ (P.depth:ℝ):= Nat.cast_le.mpr hP.enough; unfold Page.precision Tuition.need AllOrder.Catch.graded; push_cast at hx ⊢; linarith only [hx,hP.well]
 let Y x:= Access.apron G D x; let u:= -(P.depth:ℝ)/2-1
 filter_upwards [Delay.shift_pos G D, Access.wide (G:=G) (L:=D) (Rate.const (0:ℝ)), (Access.rates_apron (G:=G) (L:=D)|>.pow P.depth) P.precision ht, Access.exchange u P.depth (by unfold u; linarith only) (expired (G:=G) (D:=D) (fun x=> Bf x) _ (by linarith only [hP.lines.positive] : 0< P.a/4) u ((town (G:=G) (D:=D)).mono fun x h=>h.2.1))] with x hx h hc hv β hb
 obtain ⟨he,hh⟩:= h.2 β hb; refine ⟨(pow_le_pow_left₀ he.le hh.le _).trans ((le_abs_self _).trans hc),?_⟩
 apply le_trans _ (hv β hb); change _≤|Real.exp (-(P.a/4)*(Bf x:ℝ))|; rw [mul_comm _ (Bf x:ℝ),Real.exp_nat_mul]; exact le_abs_self _
end Page
end YM.QuadraticLocal.MintClock
