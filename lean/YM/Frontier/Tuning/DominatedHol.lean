import YM.Frontier.Tuning.Panorama

/-! Local one-variable differentiation from a measurable Cauchy envelope on the raw integrand. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.DominatedHol
open Filter Set MeasureTheory Complex Metric Function Topology
open scoped Topology
variable {α : Type*} [MeasurableSpace α] {f : ℂ→α→ℂ} {g : ℂ→α→ℂ} {ν : Measure α} {U : Set ℂ}
lemma deriv_measurable (ho:IsOpen U)(hf:∀ z∈U,AEStronglyMeasurable (f z) ν)
    (h0: ∀ a z, z∈U→ DifferentiableAt ℂ (fun c=> f c a) z) (c:ℂ)(hc:c∈U) :
    AEStronglyMeasurable (fun a=> deriv (fun t=>f t a) c) ν:=by
  classical
  obtain ⟨x,hx⟩:= exists_seq_tendsto (𝓝[≠] c)
  have hx0:∀ᶠ j in atTop,x j∈U:=hx (mem_nhdsWithin_of_mem_nhds (ho.mem_nhds hc))
  let t (z:ℂ):=if z∈U then f z else 0
  have he z: AEStronglyMeasurable (t z) ν:=by unfold t; split_ifs with ht; exact hf z ht; exact aestronglyMeasurable_zero
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun (i:ℕ)=> show AEStronglyMeasurable (fun a=> slope (fun z=> t z a) c (x i)) ν from (show AEStronglyMeasurable ((x i-c)⁻¹ • (t (x i)-t c)) ν from ((he (x i)).sub (he c)).const_smul _)) (ae_of_all _ fun a=>(((h0 a c hc).hasDerivAt.tendsto_slope).comp hx).congr' (hx0.mono (fun i h=> by simp [slope,t,hc,h])))

lemma analytic_loc (ho:IsOpen U)(hf:∀ z∈U,AEStronglyMeasurable (f z) ν)
    (h0: ∀ a z, z∈U→ DifferentiableAt ℂ (fun c=> f c a) z) (hl:∀ c∈U,∃ W∈𝓝 c,∃ h:α→ℝ,Integrable h ν ∧ ∀ z∈W,∀ a, ‖f z a‖ ≤ h a): DifferentiableOn ℂ (fun z=> ∫ a,f z a ∂ν) U:= by
    intro z hz
    obtain ⟨W,hW,h,hi,hb⟩:=hl z hz
    obtain ⟨r,hr,hR⟩:=Metric.nhds_basis_ball.mem_iff.mp (inter_mem hW (ho.mem_nhds hz))
    have hd (a) t (ht:dist t z<r/2): DiffContOnCl ℂ (fun u=> f u a) (ball t (r/2)):=by
      have he {x:ℂ} (hx:x∈ closure (ball t (r/2))) : DifferentiableAt ℂ (fun u=> f u a) x := by apply h0 a x (by refine (hR (show x∈ball z r from ?_)).2; have hh:= mem_closedBall.mp (closure_ball_subset_closedBall hx); rw [mem_ball]; exact lt_of_le_of_lt (dist_triangle x t z) (by linarith))
      exact ⟨fun x hx=>(he (subset_closure hx)).differentiableWithinAt,fun x hx=>(he hx).continuousAt.continuousWithinAt⟩
    have hb' := ae_of_all ν fun a (t:ℂ) (ht:t∈ball z (r/2))=> show ‖deriv (fun u=> f u a) t‖ ≤ h a/(r/2) from
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr) (hd a t ht) (fun y hy=> hb y (hR (mem_ball.mpr <| by have h1 := mem_sphere.mp hy; linarith [mem_ball.mp ht,dist_triangle y t z])).1 a)
    refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀:=z) (F:=f) (F':=fun z a=> deriv (fun t=>f t a) z) (ball_mem_nhds _ (half_pos hr)) ?_ (hi.mono' (hf z hz) (ae_of_all _ (hb z (mem_of_mem_nhds hW)))) (deriv_measurable ho hf h0 z hz) hb' (hi.div_const _) ?_ |>.2.differentiableAt.differentiableWithinAt
    · filter_upwards [ho.mem_nhds hz] with u hu using hf u hu
    exact ae_of_all _ fun a t ht=> (h0 a t (hR (ball_subset_ball (by linarith) ht)).2).hasDerivAt
end YM.Frontier.Tuning.DominatedHol
