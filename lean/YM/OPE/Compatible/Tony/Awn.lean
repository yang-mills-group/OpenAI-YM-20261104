import YM.OPE.Compatible.Tony.Site
import YM.OPE.Compatible.Tony.Fix
/-!
# Engel.Sensor Δ shadow angular estimate through all orders; BP Material
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
lemma pier_c (G:Gauge)(d:ℕ):∃ C:ℝ,0 ≤ C ∧∀ b n,∀ h:Board n b,∀ x:Bid.Dir G n, Roster x ≤1→ ‖iteratedFDeriv ℝ d (fun t:ℝ=> (tellerT G n).symm (Λace G h (t • x))) 0‖ ≤ C*(1+(b:ℝ))^(2*d):=by
      let a:= ‖iteratedDeriv d (fun x:ℝ=>x) 0‖; obtain ⟨c,hc,H⟩:=HearSize G d; let C:=max a c; refine ⟨C,(norm_nonneg _).trans (le_max_left ..),fun b n h x hx=> ?_⟩; let f(t:ℝ):=(tellerT G n).symm (Λace G h (t • x)); have hv: ContDiffAt ℝ ω f 0:= by
           let D:=Λace G h; let Q:ℝ→ Bid.Dir G n:=fun t=>t • x; have h0:Q 0=0:=zero_smul ..; have ht : ContDiffAt ℝ ω (D∘Q) 0:=(h0.symm ▸ haloStage h G : ContDiffAt ℝ ω D (Q 0)).comp (f:=Q) _ (contDiffAt_id.smul contDiffAt_const)
           exact (tellerT G n).symm.contDiff.contDiffAt.comp (f:=D∘Q) _ ht
      rw[norm_iteratedFDeriv_eq_norm_iteratedDeriv]; have hX:1 ≤ (1+(b:ℝ))^(2*d):= one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)); have hE:0 ≤ a:=norm_nonneg _; have hT:0 ≤ C*(1+(b:ℝ))^(2*d):= mul_nonneg (hc.trans (le_max_right ..)) (zero_le_one.trans hX); refine (pi_norm_le_iff_of_nonneg hT).2 ?_; intro i; obtain ⟨x',rfl⟩:=arkSur i; let z:= x (arkE x'); let c':=costume x'.1; have hQ:0<c':=tensile _
      let p : Bid.Dir G n→L[ℝ] G.Color:= ContinuousLinearMap.proj (arkE x'); have hp:p (iteratedDeriv d f 0)=iteratedDeriv d (p∘f) 0:=by unfold iteratedDeriv; erw[p.iteratedFDeriv_comp_left hv le_top];rfl
      change ‖p (iteratedDeriv d f 0)‖ ≤_; rw[hp]; by_cases ht:Trim b x'
      · let q: G.Color:= (tellerT G n).symm x (arkE x'); have hh:‖q‖ ≤1:= (norm_le_pi_norm ((tellerT ..).symm x) (arkE x')).trans hx; have he : p ∘ f=(fun t:ℝ=>t • q):=by funext i; change c'⁻¹ • Λace G h (i • x) (arkE x')= _; rw [vane_i,if_pos ht]; change c'⁻¹ • i • z=i • c'⁻¹ • z; rw [smul_comm]
        rw[he,iteratedDeriv_smul_const (f:=fun x:ℝ=>x) (v:=q) (by fun_prop),norm_smul]; exact ((mul_le_of_le_one_right hE hh).trans (le_max_left ..)).trans (le_mul_of_one_le_right (hE.trans (le_max_left ..)) hX)
      let q(t:ℝ):=G.plog (G.mat (hermM h (represent (t • x)) x')); have htS: p ∘ f=c'⁻¹ • q:=by funext t; change c'⁻¹ • Λace G h (t • x) (arkE x')= _; rw [vane_i, if_neg ht];rfl
      have hh: ContDiffAt ℝ ω q 0:=by
           let v(y:ℝ):=G.mat (hermM h (represent (y • x)) x'); have h0:v 0=1:=by unfold v; rw [zero_smul,link_one,herm_eye]; exact G.mat_one
           exact (h0.symm ▸ G.plog_diff : ContDiffAt ℝ ω G.plog _).comp (f:=v) 0 ((Wheat h _ G|>.contDiffAt).comp (f:=fun y:ℝ=>y • x) _ (by fun_prop)) -- binder e
      rw[htS]; rw[iteratedDeriv_const_smul (hh.of_le le_top),norm_smul]; apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans; rotate_left; · rw [norm_inv,Real.norm_of_nonneg hQ.le]; exact inv_le_one_of_one_le₀ (privilege _)
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact (H _ n h _ _ ht hx).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (zero_le_one.trans hX))
end YM.OPE.Merchant
