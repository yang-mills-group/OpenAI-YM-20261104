import YM.Integration.FVA1Physical.Wilson.ChartCollar

/-! Integrability of the independent, truncated Wilson energy on every chart.
These bounds serve only to justify linearity of the literal forest integrals. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Metric Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint Push Push.Uniform
open scoped Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {f : Side}

/-- The piecewise logarithm stays in a single finite ball, also outside the chosen
exponential patch, where it equals zero. -/
theorem chartLog_norm_bound (g : ℝ) (U : Config G f) :
    ‖chartLog g U‖ ≤ |g⁻¹| * (LocalH.geom_patch G).choose := by
  let r := (LocalH.geom_patch G).choose
  have hr := (LocalH.geom_patch G).choose_spec.1.le
  have geom := (LocalH.geom_patch G).choose_spec.2 _ le_rfl
  have bound (e : Edge (Site f)) : ‖logWithin G (U e)‖ ≤ r := by
    by_cases h : U e∈exponentialPatch G
    · rw [logWithin,Set.piecewise_eq_of_mem _ _ _ h]
      exact (mem_ball_zero_iff.mp (geom.2.2.2.2.1 h)).le
    rw [logWithin,Set.piecewise_eq_of_notMem _ _ _ h,norm_zero]
    exact hr
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg _) hr)).mpr
  intro i
  change |g⁻¹*(logWithin G (U (rope i))) i.2|≤_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (logWithin G (U (rope i))) i.2).trans (bound _)) (abs_nonneg _)

/-- Every continuous energy on the finite-dimensional Wilson coefficient chart
has a measurable, bounded pullback. No size bound on it enters the error estimate. -/
theorem chartLog_envelope (g : ℝ) {B : Positions (Primary f G) → ℝ} (hc : Continuous B) :
    Envelope (fun U : Config G f=>B (chartLog g U)) := by
  let r := |g⁻¹| * (LocalH.geom_patch G).choose
  obtain ⟨C,cap⟩ := (isCompact_closedBall (0: Positions (Primary f G)) r).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨hc.measurable.comp (chartLog_meas g),C,fun U=> cap _ (mem_closedBall_zero_iff.mpr (chartLog_norm_bound g U))⟩
end YM.Integration.FVA1Physical.Wilson
