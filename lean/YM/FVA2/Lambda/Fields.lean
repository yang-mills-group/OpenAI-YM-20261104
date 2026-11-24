import YM.FVA2.Lambda.Locus
/-!
# Fubini for the particular Gaussian moment calculation

Fubini in q and a; a here the **integration variable** on [0,1]. No lattice
estimates involved at this step. See e.g. `Try.paid`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.BranchR
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Emit MS.Pearl
open MS.City MS.Plane.Flux
open Area Shells Pages
open Lathe Gaussian
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace ENNReal NNReal
variable {G:Gauge}{a:ℝ}
local notation "Z"=> Momentum.sq (A:=Axis)
variable (α:Axis→ℕ)(i:Axis)(n:ℕ)(ha:0≤a)
abbrev Loop (f:QP×ℝ→ℝ): Prop:= Integrable f (μq.prod unitμ)
structure Try (f: QP×ℝ→ℝ)(g:ℝ→ℝ): Prop where
   pass : Loop f
   fibers (a:ℝ)(h:0≤a) : Integrable (fun q:QP=> f (q,a)) μq
   key (a:ℝ)(h:0≤a): (∫ q:QP,f (q,a)∂μq)=g a
include ha
lemma γY (q:QP): γ a q ≤ γ 0 q:= by
    unfold γ; apply Real.exp_monotone; have he:= Momentum.sq q; have ht: 0≤Momentum.sq q := by unfold Momentum.sq; exact Finset.sum_nonneg fun i _=> sq_nonneg _
    nlinarith
lemma rock_B (q:QP): ‖rock α a n q‖ ≤ ‖rock α 0 n q‖:= by unfold rock; rw [norm_mul,norm_mul (b:= γ 0 q ), Real.norm_of_nonneg ( exp_pos _|>.le ),Real.norm_of_nonneg ( exp_pos _|>.le )]; exact mul_le_mul_of_nonneg_left (γY ha _) (norm_nonneg _) 
omit ha
lemma on_f (f:ℝ→ℝ)(hf:Continuous f) : Try (fun u=>rock α u.2 n u.1*f u.2) (fun a=> tide α a n * f a) := by
    refine ⟨ ?_,fun a ha=> (gram ha α n).mul_const (f a),fun a ha=>?_⟩; swap; · change (∫ q:QP,rock α a n q * f a∂μq)=_; rw [integral_mul_const]; rfl
    have hi:Integrable f unitμ:= hf.continuousOn.integrableOn_compact isCompact_Icc
    have hx:Continuous (fun u: QP×ℝ=> rock α u.2 n u.1*f u.2):= by unfold rock γ ar Momentum.sq; fun_prop
    apply Integrable.mono (Integrable.mul_prod (gram (a:=0) (by norm_num) α n) hi) hx.aestronglyMeasurable
    have hv : ∀ᵐ p ∂(μq.prod unitμ), p.2∈Set.Icc 0 1:= Measure.quasiMeasurePreserving_snd.tendsto_ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hv] with p hp; simp only [norm_mul]; exact mul_le_mul_of_nonneg_right (rock_B α n hp.1 _ ) ( norm_nonneg _ ) -- order
variable {f g:QP×ℝ→ℝ}{j l:ℝ→ℝ}
lemma Try.add (h:Try f j)(ht:Try g l): Try (fun u=>f u+g u) (fun t=>j t+l t):= ⟨ h.pass.add ht.pass, fun a ha=>(h.fibers a ha).add (ht.fibers a ha),fun a ha=> by rw [integral_add (h.fibers a ha) (ht.fibers a ha), h.key a ha,ht.key a ha] ⟩
lemma Try.cost (h:Try f j)(ht:∀ a,0≤a→j a=l a): Try f l:= ⟨h.pass,h.fibers,fun a ha=>(h.key a ha).trans (ht a ha)⟩
lemma Try.paid (h:Try f j) : (∫ q:QP,∫ a,f (q,a)∂unitμ∂μq) = ∫ a,j a∂unitμ:= by rw [integral_integral_swap (f:=fun q:QP=>fun a:ℝ=> f (q,a)) (show _ from h.pass) ]; exact integral_congr_ae ((ae_restrict_mem measurableSet_Icc).mono fun a ha=> h.key a ha.1 )
end YM.FVA2.Lambda.BranchR
