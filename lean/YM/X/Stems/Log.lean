import YM.X.Stems.Moth
import YM.Work.F03.Flat
/-!
Log-chart order through parabola recurrence. BCH at this order without formal BCH dependencies.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Stems.Log
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Gauge Source ProjectorNext.Calibration Gauss Jet
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Pointwise
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {x y : ℝ → G.El} {z : ℝ → G.Color}
local notation "X"=> G.mat
local notation "A"=> G.colorMat

variable {a b p q:G.Color}
structure Roots (x:ℝ→G.El)(a p:G.Color) : Prop where
   lights : x 0=1
   matC : ContDiffAt ℝ ω (X ∘ x) 0
   matL : HasDerivAt (X ∘ x) (A a) 0
   matP : iteratedDeriv 2 (X ∘ x) 0= (2:ℝ) • A p+(A a)*(A a)

def shift (u v:G.Color):G.Color:= (1/2:ℝ) • G.ad u v
lemma Ex (v:G.Color)(t : ℝ): HasDerivAt (fun r:ℝ=> X (G.lieExp (r • v))) (X (G.lieExp (t • v))*A v) t:= by
   simp_rw [G.mat_lieExp,map_smul]; exact hasDerivAt_exp_smul_const (A v) t
namespace Roots
lemma Exponent (v:G.Color): Roots (fun r:ℝ=> G.lieExp (r • v)) v 0:= by
   refine ⟨by simp,(G.exp_jet.comp (contDiff_id.smul contDiff_const)).contDiffAt,?_,?_⟩
   · apply (Ex v 0).congr_deriv; simp
   simp only [show (2:ℕ)=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]; let f: ℝ→G.Mat:=fun t=> X (G.lieExp (t • v))
   change deriv (deriv f) 0 = _
   rw [show deriv f=(fun t=> f t * A v) from funext fun t=> (Ex v t).deriv]; apply Eq.trans ((Ex v 0).mul_const (A v)).deriv
   simp
lemma times (h:Roots x a p)(g:Roots y b q):Roots (x*y) (a+b) (p+q+shift a b):= by
   let f:= X ∘ x; let k:= X ∘ y; have hf : f 0=1:=by simp [f,h.lights]
   have hk : k 0=1:=by simp [k,g.lights]
   have he : X ∘ (x*y)=f*k:= funext fun u=> G.mat_mul ..
   refine ⟨by simp [Pi.mul_apply,h.lights,g.lights],he.symm ▸ h.matC.mul g.matC, ?_,?_⟩
   · rw [he]; apply HasDerivAt.congr_deriv (h.matL.mul g.matL); simp [g.lights,h.lights]
   have hl : deriv f 0=A a:=h.matL.deriv;have hm : deriv k 0=A b:=g.matL.deriv; have hq:= h.matP; have hr:=g.matP
   rw [he]; rw [iteratedDeriv_mul (h.matC.of_le (show ↑2≤ω from le_top)) (g.matC.of_le le_top)]
   change iteratedDeriv 2 f 0=_ at hq; change iteratedDeriv 2 k 0=_ at hr
   simp [Finset.sum_range_succ, iteratedDeriv_zero,iteratedDeriv_one,h.matP,g.matP,h.matL.deriv,g.matL.deriv,h.lights,g.lights,map_add,shift,map_smul, smul_add, smul_smul, G.colorMat_ad, add_mul,mul_add]
   noncomm_ring -- edit
end Roots

def record (f:ℝ→G.El): ℝ→ G.Color:= G.plog ∘ X ∘ f
namespace Roots
variable (h:Roots x a p)
include h
lemma ok : ContDiffAt ℝ ω (record x) 0:= (show ContDiffAt ℝ ω G.plog ((X ∘ x) 0) from (by rw [Function.comp_apply,h.lights,G.mat_one]; exact G.plog_diff)).comp _ h.matC
lemma zero : record x 0=0:= by simp [record,h.lights]
lemma reverse : G.lieExp ∘ record x =ᶠ[𝓝 0] x:=
   let ht : Tendsto x (𝓝 0) (𝓝 1):=((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.tendsto_nhds_iff).2 (by simpa [h.lights] using! h.matC.continuousAt.tendsto)
   ht.eventually G.plog_right
lemma first : deriv (record x) 0=a:= by
   apply G.colorMat_injective
   let f:=record x; have hf:HasDerivAt f (deriv f 0) 0:= (h.ok.differentiableAt (by simp)).hasDerivAt
   have he:= G.expDiff_zero.comp_hasDerivAt_of_eq 0 hf h.zero.symm
   exact (he.congr_of_eventuallyEq (h.reverse.symm.mono (fun u hu=> (by exact congr_arg X hu)))).unique h.matL
lemma two : iteratedDeriv 2 (record x) 0= (2:ℝ) • p:= by
   let f:=record x; let g := X ∘ G.lieExp;let e : ℝ→G.Color:=fun r=> r • a
   have he : iteratedDeriv 2 e 0=0:= by
      have he : deriv e=(fun _=>a) := funext fun t=> (by exact (show HasDerivAt e a t from (by simpa using! (hasDerivAt_id' t).smul_const a)).deriv)
      rw [show (2:ℕ)=1+1 from rfl, iteratedDeriv_succ,iteratedDeriv_one,he];simp
   have hD : deriv e 0=a:= by exact (by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const a : HasDerivAt e a 0).deriv -- edit syntax
   have hC : ContDiff ℝ ω g:= G.exp_jet
   have ht : iteratedDeriv 2 (X ∘ x) 0=iteratedDeriv 2 (g ∘ f) 0:= (show X ∘ x =ᶠ[𝓝 0] g ∘ f from h.reverse.symm.mono (q:=fun t=> (X ∘ x) t=(g ∘ f) t) (fun t ht=>congr_arg X ht)).iteratedDeriv_eq 2
   have hv : iteratedDeriv 2 (g ∘ e) 0=A a*A a:= by
      have he:= (Exponent a).matP; rw [map_zero,smul_zero,zero_add] at he; exact he
   rw [iteratedDeriv_vcomp_two (hC.contDiffAt.of_le le_top) (h.ok.of_le le_top),h.zero,h.first,h.matP] at ht; rw [iteratedDeriv_vcomp_two (hC.contDiffAt.of_le le_top) (show ContDiffAt ℝ 2 e 0 from contDiffAt_id.smul contDiffAt_const),he,show e 0=0 from zero_smul ℝ a,ContinuousLinearMap.map_zero, hD,add_zero] at hv
   rw [hv] at ht; apply G.colorMat_injective; rw [map_smul]; refine (show fderiv ℝ g 0 (iteratedDeriv 2 f 0)=A (iteratedDeriv 2 (record x) 0) from (by exact DFunLike.congr_fun G.expDiff_zero.fderiv (iteratedDeriv 2 f 0))).symm.trans (add_left_cancel ((ht.symm).trans (add_comm ..)))
lemma someL : someJ (record x) 1=a:= jo_one.trans h.first
lemma someP : someJ (record x) 2=p:= by rw [someJ,h.two]; norm_num [smul_smul]
end Roots
end YM.PositionX.Stems.Log
