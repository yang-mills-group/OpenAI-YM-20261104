import YM.MS.Arc.Estate
import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Arid
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
/-!
# Upgrading scalar holom knowledge from parameter estimates

Use contour bound on derivative and differentiation under integral (no LF-space).
 Supports even puncture via open parameter Set. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open Metric
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F][CompleteSpace F]
variable [MeasurableSpace I]
def borelad (μ:Measure I)(D:Set ℂ)(f:ℂ→ I→F): Prop:=∀ z∈D, AEStronglyMeasurable (f z) μ
variable {c:ℂ}{R:ℝ}{μ:Measure I}{D:Set ℂ}{w:I→ℝ}{f:ℂ→I→F} (hu:IsOpen D) (ht: ∀ᵐ i ∂μ, Forest D (fun z=> f z i))(hv: borelad μ D f)
-- nearby measurable derivative using U within filter
include hu ht hv
omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma Dmeas {c:ℂ}(hc:c∈D): AEStronglyMeasurable (fun i=>deriv (fun z=> f z i) c) μ:= by
   classical
   let F' (p:ℂ)(i:I): F:= if p∈D then (p-c)⁻¹ • (f p i - f c i) else 0; let U:=𝓝[≠] c
   have hP (p:ℂ): AEStronglyMeasurable (F' p) μ:= by
      by_cases hz:p∈ D; · simp_rw [F',if_pos hz]; exact ((hv p hz).sub (hv c hc)).const_smul _
      simp_rw [F', if_neg hz]; exact aestronglyMeasurable_const
   apply aestronglyMeasurable_of_tendsto_ae U hP; refine ht.mono fun i hi=> Tendsto.congr' ?_ ((hi c hc).hasDerivAt.tendsto_slope)
   filter_upwards [show D∈𝓝[≠] c from mem_nhdsWithin_of_mem_nhds (hu.mem_nhds hc)] with t ht; unfold F'; simp only [if_pos ht]; rfl
-- union not countably all test shapes. enough for each point. h activated? auto... 
omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma middle (hr:0<R)(hc: closedBall c (2*R)⊆D)(hw:Integrable w μ)(hq:∀ᵐ i ∂μ,∀ p ∈ closedBall c (2*R),‖f p i‖≤w i): HasDerivAt (fun z=>∫ i,f z i ∂μ) (∫ i, deriv (fun p=> f p i) c ∂μ) c := by
    have hδ {x} (hx : x∈ ball c R): closedBall x R ⊆ closedBall c (2*R) := fun p hp=> by rw [mem_closedBall] at hp ⊢; rw [mem_ball] at hx; nlinarith [dist_triangle p x c] -- r arbitrary
    have he : ball c R ⊆ D:= Subset.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hc
    have hC: c∈ball c R:= mem_ball_self hr
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (ball_mem_nhds c hr) (Eventually.mono (hu.mem_nhds (he hC)) (fun _ h=> hv _ h)) (F:=f) ?_ (Dmeas hu ht hv (he hC)) ?_ (bound_integrable:= hw.div_const R) ?_ (F':= fun p i=>deriv (fun q=> f q i) p)).2
    · exact hw.mono' (hv c (he hC)) (hq.mono fun i h=>h c (mem_closedBall_self (by positivity))) -- goal order
    · filter_upwards [hq,ht] with i hi h p hp; have he := hδ hp; have hZ: DifferentiableOn ℂ (fun p=> f p i) (closedBall p R):=fun z hz=> (h z (hc (he hz))).differentiableWithinAt;
      exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ⟨hZ.mono ball_subset_closedBall,by rw [closure_ball p hr.ne']; exact hZ.continuousOn⟩ (fun z hz=>hi z (he (sphere_subset_closedBall hz))) -- rw
    filter_upwards [ht] with i hi p hp; exact (hi p (he hp)).hasDerivAt
end YM.MS.Arc
