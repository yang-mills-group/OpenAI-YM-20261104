import YM.AllOrder.Laplace.Bright
/-!
 # Keep the actual Haar normalization and Bayes conditioning for changes with an address

 Extends `Laplace.Shuttle`/`Bright` to records not depending freely on either a translated
 budget or the signed orientation (they have pinned position). Important: this does *not* assert
 receipt at a different orientation. Just use the SAME torus, same tags and path y0 and same F
 and SAME unmasked target stats `Desk.art`. The vertical shift in the Gaussian chooing `.trust`
 vs `desk` is part of that representation. No cutoff limit claims not licensed by Mercury.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical
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
local notation "Ω"=> ℝ×(X×Y)

variable (P:ℝ→ Config G c)
lemma skin_compel {B:ℝ → Config G f→ℝ}(t:ℝ)(h:Envelope (B t)) (hs:S.patch.Branches S.kernel G) : Envelope (poundA F k B P t) := by
   have he : Envelope (fun U=> noiseTaylor S (P t) U k) := by
      unfold noiseTaylor; refine (Envelope.const _).mul (Envelope.sum _ _ fun i=> Env.along env_price ?_); exact measurable_const.mul ((Measurable.inv ((measurable_pi_apply i).comp (S.prediction_meas hs k))))
   unfold poundA rootA; simp_rw [div_eq_mul_inv]; exact (((Env.along (h.add he) F.continuous_drape.measurable).neg).mul (Envelope.const _)).exp

namespace Desk
variable {F O k} {B:ℝ→ Config G f→ℝ} (L:Desk F O B k) (P:ℝ→Apex c G) (W:ℝ→Poll.Body (Precision.Key F G))
variable {P W L} (hs:S.patch.Branches S.kernel G)
include hs
lemma can_anchor (hO : LocalRatio O)(h:∀ t,Envelope (B t))(hw:NextTo L.quiet P W) (r:ℝ) (hr:0<L.perk P W+r): verdict F W B (night∘P) k (L.issued P W r):= by
   let K' : ℝ×Y→ℝ := L.paid ∘ tone P W
   let A : ℝ×Y→ℝ := prepare L.high P W r
   let H t:=poundA F k B (night ∘ P) t
   let H' t y:=Real.exp (-r)*H t y
   let f:ℝ→ℝ→ℝ:= angle F (night ∘ P) W H
   let g:ℝ→ℝ→ℝ:= angle F (night ∘ P) W H'
   have he : Tendsto W (𝓝 0) (𝓝 0) := hw.w0 ▸ hw.progress.continuousAt
   have hh : ∀ᶠ δ in Tested.germ, g δ=ᶠ[Tested.germ] stick volume A K' δ:= by
      refine angle_comes F O (night ∘ P) W H' hO (Eventually.of_forall (fun i=>by exact stronglyMeasurable_const.mul ((skin_compel F k _ i (h i) hs).meas.stronglyMeasurable))) he ?_
      have hz0:Tendsto (tone P W) (𝓝 0) (𝓝 0):= (tone0 hw) ▸ (fluid hw).continuousAt
      filter_upwards [hz0.eventually L.aff] with x hx hv
      obtain ⟨p,w⟩:=x
      let z:= tone P W (p,w); let y:=H p (draw F (night (P p)) (W p+w));
      change Real.exp (-r)*y*_ = K' (p,w)*Real.exp (-(L.high z+r*p^2)/p^2)
      have hg: y* Next.SectorChange.pay O (windmill F (W p+w)) = Real.exp (-L.high z/p^2)* K' (p,w):= hx hv
      rw [mul_assoc]; change Real.exp (-r)*(y* Next.SectorChange.pay O (windmill F (W p+w)))=_
      rw [hg, show -(L.high z+r*p^2)/p^2=-r+ -L.high z/p^2 from (by have he:0<p:= hv; field_simp; ring), Real.exp_add]; ring
   have hy := ((receipted volume (approved L.pay hw hr)).moved ((hh.mono fun i hi=> hi.symm))).smul (Real.exp r)
   suffices Real.exp r • g=f by rw [this] at hy; exact hy
   funext t v; unfold g f angle H'; rw [Pi.smul_apply,Pi.smul_apply]; change Real.exp r*(_ * _)=_; rw [integral_const_mul, mul_left_comm (Real.exp r),Real.exp_neg,mul_inv_cancel_left₀ (Real.exp_pos r).ne']
lemma pension (hO:LocalRatio O)(h:∀ t,Envelope (B t))(hw:NextTo L.quiet P W):verdict F W B (night∘P) k (L.drawdown P W):=can_anchor hs hO h hw _ (by simp only [add_sub_cancel]; norm_num) -- hp

end Desk

-- no ticket `Toll` translation/reflection; compares responses to THIS kernel with *indicated* orientation/horizons. Only shifts the analytical germs; compare pert continuations on same finite period.
section pace
variable {P0:ℝ→ Config G c} (v w:ℝ→Poll.Body (Precision.Key F G))  {u y:ℕ→ℝ} {B:ℝ→ Config G f→ℝ}
variable (hv : verdict F v B P0 k u) (hW: verdict F w B P0 k y) (hs:S.patch.Branches S.kernel G)
     (hh:Tendsto P0 (𝓝 0) (𝓝 1)) (hV:Tendsto v (𝓝 0) (𝓝 0)) (hU:Tendsto w (𝓝 0) (𝓝 0)) (hb:∀ t,Envelope (B t))
include hs hh hV hU hb
private lemma coat_c : FansOut (angle F P0 v (poundA F k B P0)) (angle F P0 w (poundA F k B P0)):=by
 let M:= fun (_:ℝ)=> MeasurableEquiv.refl (F.Slice G)
 have he:Tendsto (fun p:ℝ×F.Slice G=> M p.1 p.2) (𝓝 (0,1)) (𝓝 1):= continuous_snd.continuousAt.tendsto
 apply opens (M:=M) F hh hV hh hU (Eventually.of_forall fun _=> MeasurePreserving.id _) he (Eventually.of_forall fun i _=> rfl)
 exact Eventually.of_forall fun t=> ⟨(skin_compel F k P0 t (hb t) hs).integrable _, fun _i=> (Real.exp_pos _).le⟩
include hv hW
lemma inertia_hold : u=y:= fan_unique hv hW (coat_c F k v w hs hh hV hU hb) (coat_c F k w v hs hh hU hV hb)
end pace
end YM.AllOrder.Laplace

