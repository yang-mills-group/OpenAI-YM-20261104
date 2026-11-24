import YM.MSbar.Pole.Scale.Bronze
import Mathlib.Analysis.Complex.Liouville

/-!
# A dominated analyticity test
-/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Hot
open Function Set MeasureTheory Metric Filter
open scoped Topology ContDiff Classical

variable {A : Type} [MeasurableSpace A] {μ : Measure A}

/-- Avoid a separate bill for every Laurent-order differentiation. -/
theorem diffuse {F : ℂ → A → ℂ} {z : ℂ} {b : A → ℝ} {s : Set ℂ}
    (hu : s ∈ 𝓝 z) (hm : ∀ᶠ y in 𝓝 z, AEStronglyMeasurable (F y) μ)
    (h : ∀ᵐ a ∂μ, ∀ y ∈ s, DifferentiableAt ℂ (fun z=> F z a) y ∧ ‖F y a‖ ≤ b a)
    (hb : Integrable b μ) : DifferentiableAt ℂ (fun z=> ∫ a,F z a ∂μ) z := by
  obtain ⟨R,hR,hS⟩ := Metric.mem_nhds_iff.mp hu
  let r := R/2
  have hr : 0<r := half_pos hR
  let K := ball z r
  have hh (w) (hw : w ∈ K) : closedBall w r ⊆ s := by
    intro u hu
    rw [mem_closedBall] at hu
    have he : dist w z < R/2 := hw
    exact hS (show dist u z < R from ((dist_triangle ..).trans_lt (by dsimp [r] at *; linarith : dist u w + dist w z < R)))
  have hk w (hw : w∈K) : w∈s := hh w hw (mem_closedBall_self hr.le)
  let G (w : ℂ) (a : A) := deriv (fun z=>F z a) w
  have hx := mem_of_mem_nhds hu
  have hg : AEStronglyMeasurable (G z) μ := by
    let L := 𝓝[≠] (0:ℂ)
    have hv : ∀ᶠ t in L, AEStronglyMeasurable (F (z+t)) μ := (show Tendsto (fun t:ℂ=> z+t) L (𝓝 z) from by
      simpa only [add_zero] using ((show Continuous fun t : ℂ => z+t by fun_prop).tendsto (0:ℂ)).mono_left (nhdsWithin_le_nhds (s:={(0:ℂ)}ᶜ))).eventually hm
    let H (t : ℂ) (a : A) := if AEStronglyMeasurable (F (z+t)) μ then t⁻¹*(F (z+t) a-F z a) else 0
    apply aestronglyMeasurable_of_tendsto_ae (f:=H) L
    · intro i
      by_cases e:AEStronglyMeasurable (F (z+i)) μ
      · simpa only [H,if_pos e,Pi.sub_apply] using (e.sub (mem_of_mem_nhds (x:=z) hm)).const_mul i⁻¹
      simpa only [H,if_neg e] using (aestronglyMeasurable_const (b:=(0:ℂ)))
    exact h.mono fun a ha=> ((ha z hx).1.hasDerivAt.tendsto_slope_zero).congr' (hv.mono fun w hw=> by simp only [H,if_pos hw,smul_eq_mul])
  have hp:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀:=z) (s:=K) (bound:=fun a=> b a / r) (F':=G) (μ:=μ) (F:=F) (ball_mem_nhds _ hr) hm
    (Integrable.mono' hb (mem_of_mem_nhds (x:=z) hm) (h.mono fun a ha=>(ha z hx).2)) hg
    (h.mono fun a ha w hw=> Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
        (DifferentiableOn.diffContOnCl (fun y hy=> (ha y (hh w hw (closure_ball_subset_closedBall hy))).1.differentiableWithinAt)) (fun y hy=> (ha y (hh w hw (sphere_subset_closedBall hy))).2))
    (by simpa only [div_eq_mul_inv] using hb.mul_const r⁻¹)
    (h.mono fun a ha w hw=> (ha w (hk w hw)).1.hasDerivAt)
  exact hp.2.differentiableAt

end YM.SchemeRG11.Hot
