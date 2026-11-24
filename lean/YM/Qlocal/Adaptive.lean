import YM.Qlocal.BindPulse
import YM.AllOrder.Docket.Panorama
/-! Extend AllOrder/Laplace/Bright & Spin: the chamber of choices in boosts
 need not be equivariant under orientations/path changes. Fixed vertical
 order. Compare shift only (no rotation, area scaling elsewhere). -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical
open AllOrder Laplace
open Lattice Wilson RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext Repeat Lapis Lantern Fare Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat
open scoped BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}
variable (F: Forest S.ratio) (O: ChartRatio G)(k:S.Choices)
local notation "K"=>Precision.Key F G
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "X"=> Apex c G


variable {B:ℝ → Config G f→ℝ} (P:ℝ → Config G c)(t:ℝ)(h: Envelope (B t)) (hs:S.patch.Branches S.kernel G)
include hs h
lemma compelling : Envelope (poundA F k B P t) := by
   have he : Envelope (fun U=> noiseTaylor S (P t) U k) := by
      unfold noiseTaylor; refine (Envelope.const _).mul (Envelope.sum _ _ fun i=> Env.along env_price ?_); exact measurable_const.mul ((Measurable.inv ((measurable_pi_apply i).comp (S.prediction_meas hs k))))
   unfold poundA rootA; simp_rw [div_eq_mul_inv]; exact (((Env.along (h.add he) F.continuous_drape.measurable).neg).mul (Envelope.const _)).exp

namespace Grant
open Desk
omit h
variable {F O k P} {Q:ℝ→Apex c G}{L:Desk F O B k}{W:ℝ→Poll.Body (Precision.Key F G)}
lemma agreed (hO : LocalRatio O)(h:∀ t,Envelope (B t))(hw:NextTo L.quiet Q W) (r:ℝ) (hr:0<L.perk Q W+r): verdict F W B (night∘Q) k (L.issued Q W r):= by
   let K' : ℝ×Y→ℝ := L.paid ∘ tone Q W
   let A : ℝ×Y→ℝ := prepare L.high Q W r
   let H t:=poundA F k B (night ∘ Q) t
   let H' t y:=Real.exp (-r)*H t y
   let f:ℝ→ℝ→ℝ:= angle F (night ∘ Q) W H
   let g:ℝ→ℝ→ℝ:= angle F (night ∘ Q) W H'
   have he : Tendsto W (𝓝 0) (𝓝 0) := hw.w0 ▸ hw.progress.continuousAt
   have hh : ∀ᶠ δ in Tested.germ, g δ=ᶠ[Tested.germ] stick volume A K' δ:= by
      refine angle_comes F O (night ∘ Q) W H' hO (Eventually.of_forall (fun i=>by exact stronglyMeasurable_const.mul ((compelling F k _ i (h i) hs).meas.stronglyMeasurable))) he ?_
      have hz0:Tendsto (tone Q W) (𝓝 0) (𝓝 0):= (tone0 hw) ▸ (fluid hw).continuousAt
      filter_upwards [hz0.eventually L.aff] with x hx hv
      obtain ⟨p,w⟩:=x
      let z:= tone Q W (p,w); let y:=H p (draw F (night (Q p)) (W p+w));
      change Real.exp (-r)*y*_ = K' (p,w)*Real.exp (-(L.high z+r*p^2)/p^2)
      have hg: y* Next.SectorChange.pay O (windmill F (W p+w)) = Real.exp (-L.high z/p^2)* K' (p,w):= hx hv
      rw [mul_assoc]; change Real.exp (-r)*(y* Next.SectorChange.pay O (windmill F (W p+w)))=_
      rw [hg, show -(L.high z+r*p^2)/p^2=-r+ -L.high z/p^2 from (by have he:0<p:= hv; field_simp; ring), Real.exp_add]; ring
   have hy := ((receipted volume (approved L.pay hw hr)).moved ((hh.mono fun i hi=> hi.symm))).smul (Real.exp r)
   suffices Real.exp r • g=f by rw [this] at hy; exact hy
   funext t v; unfold g f angle H'; rw [Pi.smul_apply,Pi.smul_apply]; change Real.exp r*(_ * _)=_; rw [integral_const_mul, mul_left_comm (Real.exp r),Real.exp_neg,mul_inv_cancel_left₀ (Real.exp_pos r).ne']
lemma awarded (hO:LocalRatio O)(h:∀ t,Envelope (B t))(hw:NextTo L.quiet Q W):verdict F W B (night∘Q) k (L.drawdown Q W):=agreed hs hO h hw _ (by simp only [add_sub_cancel]; norm_num) -- hp

variable {V:ℝ→Poll.Body (Precision.Key F G)}(hp:Tendsto P (𝓝 0) (𝓝 1))(hE:∀ t,Envelope (B t))(hV:Tendsto V (𝓝 0) (𝓝 0))(he:Tendsto W (𝓝 0) (𝓝 0))
include hE hV he hp
lemma awards {F':ℕ→ℝ}{R:ℕ→ℝ}(h' : verdict F W B P k F')(h0:verdict F V B P k R):F'=R:= by
 have hM : ∀ᶠ t in Tested.germ, let f':= poundA F k B P t; Integrable f' (F.order G) ∧ 0≤ f' := Eventually.of_forall fun t=> ⟨(compelling F k P t (hE t) hs).integrable _, fun _i=> (Real.exp_pos _).le⟩
 let T₀:= F.Slice G; let M:= MeasurableEquiv.refl T₀

 refine fan_unique h' h0 (opens (M:=fun i=> M) F hp he hp hV ?_ ?_ ?_ hM) (opens (M:=fun i=> M) F hp hV hp he ?_ ?_ ?_ hM); all_goals first| exact Eventually.of_forall fun t=> MeasurePreserving.id _ | exact continuous_snd.continuousAt.tendsto | exact Eventually.of_forall fun t hv=>rfl
omit hV he hp
open Laplace.SigmaP Response PositionX.Jet
lemma income (x:Apex c G)(hk:0< L.paid 0)(hO:LocalRatio O) : logS (L.drawdown (course x) (L.quiet ∘ course x))=Function.swap (ratePlan L) x:= by
 let P':= echo (fun _ : ℝ=> x); let hT:= lends (ρ:=L.quiet) (P:=fun _=>x) contDiffAt_const; let H:=belong L.pay.steer hT.p0 hT.cont
 have hp: ContDiffAt ℝ ω (fun _ : ℝ=> x) 0:= contDiffAt_const
 have hu: grants L (fun _=>x)=L.drawdown P' (L.quiet ∘ P'):= by
   exact awards hs (light_courier hp) hE (H.w0 ▸ H.progress.continuousAt) (hT.w0 ▸ hT.progress.continuousAt) (awarded hs hO hE hT) (awarded hs hO hE H)
 rw [show course x=P' from rfl,← hu]; exact (Response.logprice L hp hk).trans (weigh_const _)
end Grant
end YM.Qlocal.Bind
