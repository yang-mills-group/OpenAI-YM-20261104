import YM.Qlocal.Adaptive
/-!
 # Full real pole J. Use window-positive ramps + canonical Fk.
   No β redistribution.Aperture.The test sup and all-marker product delivered in
   PLUS and MINUS stabs. Pole charge q before orientation absorbed by extra g.
   Work first in ℝ, derive a true strong full-real estimate with ALL normalized-on-coordinate-derivatives
   (then reconstruct gauges across shifts). Never infer marker radius norm from one evaluation.
   Envelope condition on pre-damped columns separate. R is unscaled mask exponent letter of a log mark (later use with combination of several as well, via closure under products with corresponding rank shifts). May use any stencil supports during construction; here Fk independent thereof.
   Paint-independent test space Ω not yet bound until integration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}

abbrev reed (G:Gauge)(n:Side):=ℝ→ Config G n→ℝ
variable (R : reed G n)
structure Flute (R : reed G n)(q:ℕ):Prop where
   byfield (s : ℝ): GaugeInvariant (R s)
   envelope (s : ℝ) : RG.Envelope (R s)
   zeroAt : GradeAt q (Comparison.RG02.Bulk.projected R)

namespace tether
def ramp (s:ℝ):ℝ:= 1+s+s^2
def road : ℝ→ℝ:= Real.log ∘ ramp
lemma ramp_ge(s:ℝ):1/2≤ ramp s:=by unfold ramp; nlinarith [sq_nonneg (s+1/2)]
lemma openr(s:ℝ): 0 < ramp s:= lt_of_lt_of_le (by norm_num) (ramp_ge s)
lemma clear_path (s:ℝ): Real.exp (road s)=ramp s:= Real.exp_log (openr s)
lemma none_path : road 0=0:= by simp [road,ramp]
lemma paved : ContDiff ℝ ω ramp:= by unfold ramp; fun_prop
lemma silk : ContDiff ℝ ω road:= paved.log fun x=> (openr x).ne'
abbrev fig (R:reed G n)(b:ℝ)(t:ℝ)(x:Config G n):= b*t* R t x
abbrev color (R:reed G n)(b:ℝ)(t:ℝ): Config G n→ℝ:= ramp ∘ fig R b t
def line (R:reed G n)(b t:ℝ)(x: Config G n):= t^2 * road (fig R b t x)
variable (hs:Flute R q)
include hs
-- prices and ν.Inv: Tilt supports remain adequate when adding a finite-width perturb independent of actual step at physical density. Don't claim uniformity auxiliary here.
omit hs in
lemma alongpath (f:ℝ→ℝ)(W: Config G n→ℝ) (hf:Continuous f)(hw:RG.Envelope W): RG.Envelope (f ∘ W):= by
 obtain ⟨w,hx⟩:= hw.cost; obtain ⟨a,ha⟩:= (isCompact_closedBall (0:ℝ) w).image (continuous_norm.comp hf) |>.bddAbove; refine ⟨hf.measurable.comp hw.meas,a,fun u=> ha (?_)⟩; exact Set.mem_image_of_mem _ (mem_closedBall_zero_iff.mpr (hx u))
lemma holler (b t:ℝ): RG.Envelope (fig R b t):=(Envelope.const _).mul (hs.envelope t)
lemma real_cost (b t:ℝ): RG.Envelope (color R b t):= alongpath _ _ paved.continuous (holler R hs b t)
lemma first (b t:ℝ): RG.Envelope (line R b t):= (RG.Envelope.const _).mul (alongpath _ (fig R b t) silk.continuous (holler R hs b t))
lemma sky (b t:ℝ): GaugeInvariant (color R b t):= fun z y=>congr_arg ramp (show _= _ from (congr_arg ((b*t)* ·) (hs.byfield t z y))) -- enough
lemma rock (b t:ℝ): GaugeInvariant (line R b t):= by intro z y; dsimp only [line, fig]; rw [hs.byfield t z y]
-- marker pank.Intangible grade exactly p rank.S. for Fuel poles. Fast packing retains amplitude.E.
lemma voice (b:ℝ): GradeAt 3 (Comparison.RG02.Bulk.projected (line R b)):= by
 let f:= Comparison.RG02.Bulk.projected R; let l (z:ℝ×Bid.Dir G n):= fig R b z.1 (represent z.2); have hf:ContDiffAt ℝ ω l 0:= ((contDiffAt_const.mul (show ContDiffAt ℝ ω (@Prod.fst ℝ (Bid.Dir G n)) 0 from contDiffAt_fst)).mul hs.zeroAt.smooth); have hp:l 0=0:= by simp [l,fig]
 exact (GradeAt.shifts (@Prod.fst ℝ (Bid.Dir G n)) contDiffAt_fst rfl 2).mul (GradeAt.anchored (silk.contDiffAt.comp (f:=l) _ hf) (hp.symm ▸ none_path)) -- motive
end tether
section formula
open tether
variable (F:Forest S.ratio){O:ChartRatio G}{s:Clip}{U:PathData G}(T:S.Choices) (W: Layout G)(A:Finset Age)(h:Legal A W)(X : reed G f)(u:ℝ)
local notation "E"=>ℝ×(Apex c G × Poll.Body (Precision.Key F G))
abbrev build (X:reed G f)(u:ℝ): E→ℝ:= (Comparison.RG02.Bulk.posed S F (line X u)) ∘ (Binding.gaugeL F)
abbrev changes (X:reed G f)(u:ℝ)(V: Finset Age): E→ℝ:=venue F W V- build F X u
local notation "H"=> changes F W X u A
variable {B0:ℝ→ Config G f→ℝ}
local notation "Γ"=> B0-line X u
variable (D:Desk F O B0 T)(hs: Flute X q)
include hs
lemma bridge_rent : GradeAt 3 (build F X u):= GradeAt.coarse (f:=Comparison.RG02.Bulk.posed S F _) (g:= Binding.gaugeL F) (Comparison.RG02.Bulk.joint_receipt S F (voice X hs u)) ((Binding.gaugeL F).contDiff.contDiffAt) ((Binding.gaugeL F).map_zero)
-- raiseV using `Catch.Flood` via this. Financial proof later.
include h
lemma slope : Rise H := by
 have ht:= smoothV F W A h; let hb:=bridge_rent F X u hs; constructor; exact ht.1.sub hb.smooth; intro i hi; ext1 x; have hx : Radial.jet (-build F X u) i x=0:= by simp [Radial.jet,iteratedFDeriv_neg_apply, hb.vanish i (by omega)]; --
 unfold changes; rw [sub_eq_add_neg, Laplace.jet_add ht.1 (show ContDiffAt ℝ ω (-build F X u) 0 from hb.smooth.neg), hx, ht.2 i hi]; exact add_zero _
abbrev risky (B0:ℝ→ Config G f→ℝ)(s:Finset Age)(u:ℝ)(X:reed G f):= spend W s B0 - line X u
noncomputable def boost: Desk F O (risky W B0 A u X) T where
 hard := D.hard
 quiet:= D.quiet
 paid:= D.paid
 high:= D.high+ H
 pay:= by refine ⟨D.pay.steer,D.pay.activity.add (slope F W A h X u hs).1,fun i hi=> ?_,D.pay.ample⟩; ext1 x; rw [Laplace.jet_add D.pay.activity (slope F W A h X u hs).1,(slope F W A h X u hs).ranks _ hi,D.pay.rank _ hi]; exact add_zero _
 aff:= by
    filter_upwards [(augment F W A D h).aff] with z hz hi; let y:= represent (Uniform.tint G _ z.2.1); let I:= draw F y z.2.2; let s:= z.1
    let V:=F.drape I; let a:= line X u s V; let J:= spend W A B0 s V; let g:= noiseTaylor S y V T; let w:ℝ:= Next.SectorChange.pay O (windmill F z.2.2); have he : Real.exp (-(J +g)/s^2)*w= Real.exp (-((augment F W A D h).high z)/s^2)*D.paid z:= hz hi
    intro t; let d:= z.2; change Real.exp (-(J-a+g)/s^2)*w= Real.exp (-(D.high z+(venue F W A z-build F X u z))/s^2)* D.paid z; rw [show -(J - a + g)/s^2=a / s^2 + -(J+g)/s^2 by ring,Real.exp_add,mul_assoc, he, ←mul_assoc,← Real.exp_add]; refine congr_arg (fun x:ℝ=> Real.exp x*D.paid z) ?_; change _ = -(D.high z+(venue F W A z-a))/s^2; simp only [Floe.augment,Pi.add_apply]; ring
end formula
end YM.Qlocal.Bind
