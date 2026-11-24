import YM.AllOrder.Docket.Fate
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Aux
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PertExtension.Series Laplace Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open Catch Catch.Clock Sienna 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι:Type*}{T:Catch.Clock ι} {W b D α a B C Ω κ V:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
namespace Name
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K (k+3)}
variable (A: Aux.Name G P K u x r k U)
local notation "I"=>Aux.Name G P K u x r k U
local notation "ξ"=> Aux.scope x
local notation "b"=> A.beta
local notation "d"=> A.Θ
local notation "Θ"=> A.price.threshold
open Till Tilt Lantern
abbrev fi (i:Age)(U:Config G A.f):= Extra.Iteration.action (A.shape i) U
abbrev uncloud (U:Config G A.f) :ℝ:= -(b)*∑ i∈ξ, d^i.stamp* A.fi i U
variable (Q:Age→ℝ)(h:A.Civil Q) (V:Config G A.f)
abbrev tuition (i:Age):= Step.PlanV.authority (Burn.horizon x) i (Step.PlanV.strengthP A.due)
abbrev bid (i:Age):= (A.vol:ℝ)*(A.tuition i*Θ^i.r)
abbrev unpriced (A:Aux.Name G P K u x r k U):= ∑ i∈ Aux.scope x,A.Θ^i.stamp* A.bid i
abbrev tailFee (A:Aux.Name G P K u x r k U)(Q:Age→ℝ)(i:Age):= (A.vol:ℝ)*((Real.exp (-(Q i/2)*A.price.B)*A.tuition i) *A.price.threshold^i.r)
abbrev diffFee (A:Aux.Name G P K u x r k U)(Q:Age→ℝ):= A.beta*∑ i∈ξ,A.Θ^i.stamp*(A.tailFee Q i+A.tailFee Q i)
include h
lemma story (i:Age)(hp:i∈ξ)(hv: flags A.price.threshold V=∅) : |A.fi i V|≤ A.bid i:= by
 let hQ:=h.handy i hp; let t:=Θ; refine brine (f:=fun s=> Precision.uncut (A.shape i) (pull s (0:Site A.f) V)) fun s=>?_; have he:= ozone A.price _ (Pane.tranquility _ hv s 0) _ (h.sk _) hQ.pay; exact he.trans (mul_le_mul_of_nonneg_right (A.loom.finalP) (mul_nonneg (budget_nonneg hQ.pay) (pow_nonneg A.price.threshold_pos.le _))) -- defeq Prec?
lemma uncloud_price (hv:flags A.price.threshold V=∅): |A.uncloud V| ≤ b*A.unpriced:= by
 unfold uncloud; rw [abs_mul,abs_neg,abs_of_pos A.bpos]; refine mul_le_mul_of_nonneg_left ?_ A.bpos.le; refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i hi=> ?_)); rw [abs_mul,abs_of_pos (pow_pos A.Θp _)]; exact mul_le_mul_of_nonneg_left (story A Q h V i hi hv) (pow_pos A.Θp _).le
lemma pay_tail (i:Age)(hp:i∈ξ)(hv:flags A.price.threshold V=∅):
  let U:=legible (A.shape i) A.price.B; |A.fi i V-Extra.Iteration.action U V| ≤ A.tailFee Q i+A.tailFee Q i:= by
 intro U; obtain ⟨X,Y,H,hX,hY⟩:= action_slips _ (h.handy i hp).pay (h.sk _) A.price.B; have hh (a:ℕ→Atom G i.r)(he: Charged a (Q i/2) (Real.exp (-(Q i/2)*A.price.B)*A.tuition i)) : |Extra.Iteration.action a V| ≤ A.tailFee Q i:= by
     refine brine (f:=fun s=>Precision.uncut a (pull s (0:Site A.f) V)) fun s=>?_; have hx:= ozone A.price _ (Pane.tranquility _ hv s 0) _ (half_pos (h.sk _)) he; exact hx.trans (mul_le_mul_of_nonneg_right (A.loom.finalP) (mul_nonneg (budget_nonneg he) (pow_nonneg A.price.threshold_pos.le _)))
 unfold fi U; rw [H]; exact (abs_sub _ _).trans (add_le_add (hh X hX) (hh Y hY)) -- abs_sub syntax
lemma odds (hvB : 4*(Burn.horizon x+4)≤ A.price.B)(hv: flags A.price.threshold V=∅): |A.view V- A.uncloud V|≤ A.diffFee Q:= by
 have hx : -A.view V=b*∑ i∈ξ,d^i.stamp*Extra.Iteration.action (legible (A.shape i) A.price.B) V:= by
    unfold view; rw [neg_neg]; apply Eq.symm (Tilt.sunset (A:=A.shape) (X:=ξ) A.price.B (fun i hi=>?_) d A.Θp b (gS _ A.bpos|>.2) _)
    apply le_trans (Nat.mul_le_mul_left 4 (i.pricey.trans (Nat.add_le_add_right (Age.in_scope.mp hi) 2))) hvB
 unfold uncloud; rw [← neg_neg (A.view _),hx,neg_mul,neg_sub_neg,← mul_sub,← sum_sub_distrib, abs_mul,abs_of_pos A.bpos]; refine mul_le_mul_of_nonneg_left ?_ A.bpos.le; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum ?_); intro i hi; rw [← mul_sub,abs_mul,abs_of_pos (pow_pos A.Θp _)]; exact mul_le_mul_of_nonneg_left (pay_tail A Q h V i hi hv) (pow_pos A.Θp _).le
-- Envelope unmask beyond Caller V-aligned.Proof cost any flags/legs. not asserting Exp small there
omit h
lemma upEnv : RG.Envelope (Real.exp ∘ A.uncloud):= by
 let f i:=Extra.Iteration.action (A.shape i) (n:=A.f); have hx i (hi:i∈ξ): RG.Envelope (f i):= by
    obtain ⟨a,C,ht,hv⟩:=A.legal.rent i hi; exact (RG.Envelope.const _).mul (RG.Envelope.sum _ _ fun l=> Env.along (env_uncut hv ht) (continuous_pull l 0|>.measurable)); -- env sum namespace binder
 -- finite.Nonuniv.Sure. lemma names.
 let g (j:Age) (V:Config G A.f):= d^j.stamp*A.fi j V; let E s:= RG.Envelope (fun V=>∑ j∈s, g j V); have he s (h:s⊆ξ): E s:= by
    induction s using Finset.induction_on with
    | empty=> unfold E; simp only [sum_empty]; exact RG.Envelope.const 0
    | insert i s hz ih => unfold E; simp only [sum_insert hz]; exact ((RG.Envelope.const _).mul (hx i (h (mem_insert_self ..)))).add (ih fun j hj=> h (mem_insert_of_mem hj))
 exact ((RG.Envelope.const (-(b))).mul (he ξ (subset_refl _))).exp
namespace Proper
variable (W:ι→ Aux.Name G P K u x r k U) (hQ:Proper W T)
local notation "ζ"=> T.Meter
local notation "L"=> Burn.horizon x
include hQ
lemma fare : ζ (fun i=>(W i).beta*(W i).unpriced) (-(3/2:ℝ)) := by
 unfold unpriced; simp_rw [Finset.mul_sum]; apply Clock.Meter.sum; intro v hv
 let F₁:= counts W hQ; let hH:= F₁.unitPay le_rfl ((hire W hQ v).unitPay le_rfl ((cheap W hQ).pow v.r)); let H₀:= (Proper.meter W hQ).1.pow v.stamp; refine ( (strength W hQ).mul (H₀.mul hH)).weak ?_; have hw:v.e+2=v.stamp+v.r:= v.recovery; have ht:v.grade+3=v.e:=rfl; have hz:= Nat.cast_le (α:=ℝ)|>.mpr (show 5≤v.stamp+v.r from (by omega)); push_cast at hz ⊢; linarith only [hz] -- need push
lemma melt_tail (s:Age→ℝ)(hh:∀ i,0<s i)(g:ℝ): ζ (fun i=>(W i).diffFee s) g:= by
 let v:=g-1; unfold diffFee; refine Clock.Meter.weak (Clock.Meter.mul (strength W hQ) («b»:=v) ?_) (by unfold v; linarith)
 apply Clock.Meter.sum; intro y hy; let S' i:= (W i).tailFee s y; have hp: ζ S' v:= by
     unfold S' tailFee; let hx:= (counts W hQ); let p (x:ι):= Real.exp (-(s y/2)*(W x).price.B); have hz: T.Meter p v:= by exact (hQ.look.melt v (half_pos (hh y))).eq_mem ((windowB W hQ).mono fun i hi=> (show _=p i from (by dsimp only [p]; rw [hi]))); -- melt arg parse
     exact hx.unitPay le_rfl (((hz.mul (hire W hQ y)).mul ((cheap W hQ).pow y.r)).weak (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) y.r]));
 exact ((meter W hQ).1.pow y.stamp).unitPay (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) y.stamp]) (hp.add hp)
lemma region_ok : ∀ᶠ i in T.rail, 4*(L+4)≤ (W i).price.B:=by
 filter_upwards [ (Work.E01.radiusB_tendsto.comp (T.drive.congr' hQ.look.same)).eventually_ge_atTop (4*(L+4)), Proper.windowB W hQ] with i hi ht; rw [ht]; exact hi
lemma bandwidth (z:ℝ)(hz:z<0) : ∀ᶠ i in T.rail, ∀ V:Config G (W i).f, flags (W i).price.threshold V=∅ → |(W i).view V -(W i).uncloud V|≤ T.cost i^z ∧ |(W i).view V|≤1:= by
 obtain ⟨s,hs,hS⟩:=hQ.legible; let hP:= Clock.Meter.pale T z; filter_upwards [hS,melt_tail W hQ s hs (z-1) z (by linarith),(fare W hQ).low (by norm_num) (by norm_num : (0:ℝ)<1/2),region_ok W hQ,hP.low hz (by norm_num : (0:ℝ)<1/2)] with i hi hm hM he hX V hv; have hT:= (odds _ s hi V he hv).trans ((le_abs_self _).trans hm); refine ⟨hT,?_⟩; rw [← sub_add_cancel ((W i).view V) ((W i).uncloud V)]; refine (abs_add_le ..).trans ?_; linarith only [hT, le_of_lt hX,hM, uncloud_price _ _ hi V hv,le_abs_self ((W i).beta*(W i).unpriced),le_abs_self (T.cost i ^ z)]
end Proper
end Name
end YM.AllOrder.Aux
