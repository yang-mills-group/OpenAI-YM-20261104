import YM.AllOrder.Laplace.Star
import YM.AllOrder.Laplace.Shuttle
/-!
# Conditional Test Γ with only the hard action and its primitive trial

`Desk.can_compete` gives a real-purpose conclusion: an exact finite-dimensional
Laplace comparison without global β/regulator assertions, independent uniform μ supplied
later. `earn`: the Γ is an independent construction from Taylor jets of the trial A,σ & ψ and
full normalized vertical kernel. Needs NO many-step limit at this post.
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
abbrev Apex (c:Side)(G:Gauge):= Positions (Uniform.Primary c G)
local notation "K"=>Precision.Key F G
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "X"=> Apex c G
local notation "Ω"=> ℝ×(X×Y)
-- import? if unknown def
structure Desk (F:Forest S.ratio)(O:ChartRatio G) (B:ℝ → Config G f→ℝ)(k:S.Choices) where
  hard : Apex c G × Poll.Body (Precision.Key F G) → ℝ
  quiet : Apex c G→Poll.Body (Precision.Key F G)
  high : ℝ×(Apex c G × Poll.Body (Precision.Key F G))→ℝ
  paid : ℝ×(Apex c G × Poll.Body (Precision.Key F G))→ℝ
  pay : Treaty hard quiet high paid
  aff : ∀ᶠ x in 𝓝 (0:ℝ×(Apex c G × Poll.Body (Precision.Key F G))), 0<x.1 →
     let V:= represent (Uniform.tint G _ x.2.1)
     poundA F k B (fun _=> V) x.1 (draw F V x.2.2)* Next.SectorChange.pay O (windmill F x.2.2)= Real.exp (-high x / x.1^2)*paid x
namespace Desk
variable {F O k}{B:ℝ → Config G f→ℝ} (L:Desk F O B k) (P:ℝ→Apex c G) (W:ℝ→Poll.Body (Precision.Key F G))
def night {c:Side} {G:Gauge} (p:Apex c G): Config G c:= represent (tint G _ p)
noncomputable def perk:ℝ:= curvature L.hard (fderiv ℝ P 0 1) (fderiv ℝ W 0 1)
def issued (r:ℝ) : ℕ→ℝ:= Real.exp r • part volume (prepare L.high P W r) (L.paid ∘ tone P W)
/-- canonical all-order jets. `ξ` threshold unchanged, no winding claims at registration -/
def drawdown := L.issued P W (1-L.perk P W)
variable {P W L} (hs:S.patch.Branches S.kernel G)
include hs
lemma can_compete (hO : LocalRatio O)(h:∀ t,Toll f (B t))(hw:NextTo L.quiet P W) (r:ℝ) (hr:0<L.perk P W+r): verdict F W B (night∘P) k (L.issued P W r):= by
   let K' : ℝ×Y→ℝ := L.paid ∘ tone P W
   let A : ℝ×Y→ℝ := prepare L.high P W r
   let H t:=poundA F k B (night ∘ P) t
   let H' t y:=Real.exp (-r)*H t y
   let f:ℝ→ℝ→ℝ:= angle F (night ∘ P) W H
   let g:ℝ→ℝ→ℝ:= angle F (night ∘ P) W H'
   have he : Tendsto W (𝓝 0) (𝓝 0) := hw.w0 ▸ hw.progress.continuousAt
   have hh : ∀ᶠ δ in Tested.germ, g δ=ᶠ[Tested.germ] stick volume A K' δ:= by
      refine angle_comes F O (night ∘ P) W H' hO (Eventually.of_forall (fun i=>by exact stronglyMeasurable_const.mul ((env_compel F k _ i (h i) hs).meas.stronglyMeasurable))) he ?_
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
lemma award (hO:LocalRatio O)(h:∀ t,Toll f (B t))(hw:NextTo L.quiet P W):verdict F W B (night∘P) k (L.drawdown P W):=can_compete hs hO h hw _ (by simp only [add_sub_cancel]; norm_num) -- hp
end Desk
end YM.AllOrder.Laplace
