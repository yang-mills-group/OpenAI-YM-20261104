import YM.FormalOPE.RG10.BlockGauge.Identity
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
/-!
 # Transferring strict stationary Hessian for joint gauge calculation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E F : Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]

lemma second {f:F→ℝ}{k:E→F}(hk:ContDiffAt ℝ ω k 0) (hc:k 0=0)(hf:ContDiffAt ℝ ω f 0)(hh:fderiv ℝ f 0=0)(u:E):
 jet (f ∘ k) 2 u=jet f 2 ((fderiv ℝ k 0) u):= by
 have hf': ContDiffAt ℝ ω f (k 0):= hc.symm ▸ hf
 let g:= fderiv ℝ f ∘ k
 let q:= fderiv ℝ k
 have h₁: ContDiffAt ℝ ω g 0:= (hf'.fderiv_right le_top).comp _ hk
 have h₂: ContDiffAt ℝ ω q 0:= hk.fderiv_right le_top
 have hv: fderiv ℝ (f ∘ k) =ᶠ[𝓝 0] (fun y=> (g y).comp (q y)):= by
  filter_upwards [hk.eventually (by simp), hk.continuousAt.eventually (hf'.eventually (by simp))] with y hy hv; exact fderiv_comp y (hv.differentiableAt (by simp)) (hy.differentiableAt (by simp))
 have he: fderiv ℝ (fderiv ℝ (f ∘ k)) 0 = ((ContinuousLinearMap.compL ℝ E F ℝ).flip (q 0)).comp (fderiv ℝ g 0):= by rw [hv.fderiv_eq, fderiv_clm_comp (h₁.differentiableAt (by simp)) (h₂.differentiableAt (by simp)), show g 0=0 from by simp [g,hc,hh]]; simp
 have hm := fderiv_comp (g:=fderiv ℝ f) (0:E) ((hf'.fderiv_right (m:=ω) le_top).differentiableAt (by simp)) (hk.differentiableAt (by simp))
 rw [hc] at hm -- product type on same power
 unfold jet; simp_rw [iteratedFDeriv_two_apply,he]
 simp [g,hm,q]

lemma stable {h:E→ℝ}(hf: ContDiffAt ℝ ω h 0)(hb: h 0=0)(hh:∀ x,0≤h x): Stationary h where
 base0:=hb
 base1 x:= by
   have hx:fderiv ℝ h 0=0:=(show IsLocalMin h 0 from Filter.Eventually.of_forall (p:=fun u=> h 0≤h u) fun u=> hb.symm ▸ hh u).fderiv_eq_zero
   unfold jet; rw [iteratedFDeriv_one_apply]; simp [hx]
 smooth := hf.of_le le_top

lemma same_jet {k l:E→ℝ}(h:k =ᶠ[𝓝 0] l)(n:ℕ)(u:E) : jet k n u=jet l n u:= by unfold jet; rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h n).eq_of_nhds]
end YM.FormalOPE.RG10.Inherit
