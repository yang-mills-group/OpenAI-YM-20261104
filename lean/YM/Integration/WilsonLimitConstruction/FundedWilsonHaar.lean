import YM.XSpace.Bare
import YM.PertExtension.BareChart

/-! The product probability Haar chart on all original links of the finite
Wilson lattice. Its chamber radius is fixed before the cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonHaar

open Filter Set Metric MeasureTheory Lattice Wilson RG PertExtension
open scoped Topology ContDiff
variable {G : Gauge} {n : Side}

def radius (G : Gauge) : ℝ := Chart.small G (XSpace.Bare.chart G)
theorem radius_pos (G : Gauge) : 0 < radius G := Chart.Ratio.small_pos (XSpace.Bare.chart_ratio G)

def integrand (β : ℝ) (O : Config G n → ℝ) (x : Directions G n) : ℝ :=
  let U := Chart.expLinks G (Edge (Site n)) x
  Chart.jacobian (XSpace.Bare.chart G) x * (bare β U * O U)

theorem change (β : ℝ) (O : Config G n → ℝ) (hO : Measurable O)
    {r : ℝ} (hr : r < radius G) (hpos : 0 < r) :
    (∫ U in Chart.chamber G (Edge (Site n)) r, bare β U * O U ∂prior G n) =
      ∫ x in ball (0 : Directions G n) r, integrand β O x ∂Chart.tangent G (Edge (Site n)) :=
  Chart.Ratio.chamber_integral (U := Edge (Site n)) (XSpace.Bare.chart_ratio G)
    (fun U => bare β U * O U) ((measurable_bare β).mul hO) hr hpos

/-- The ordinary finite-dimensional dilation includes its dimensional power.
The chart still integrates over the full physical index set, with a single
linkwise-valid chamber radius. -/
theorem scaled (β : ℝ) (O : Config G n → ℝ) (hO : Measurable O)
    {r t : ℝ} (hr : r < radius G) (hpos : 0 < r) (ht : 0 ≤ t) :
    (t ^ Module.finrank ℝ (Directions G n))⁻¹ *
      (∫ U in Chart.chamber G (Edge (Site n)) r, bare β U * O U ∂prior G n) =
        ∫ x in Series.Radial.disc t r, integrand β O (t • x) ∂Chart.tangent G (Edge (Site n)) := by
  rw [change β O hO hr hpos]
  let A := ball (0 : Directions G n) r
  let D := Series.Radial.disc (E := Directions G n) t r
  let f := integrand β O
  have hI (x : Directions G n) : A.indicator f (t • x) =
      D.indicator (fun y => f (t • y)) x := by
    by_cases h : t • x ∈ A
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ D from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ D from h)]
  have hs := Measure.integral_comp_smul_of_nonneg (Chart.tangent G (Edge (Site n)))
    (A.indicator f) t (hR := ht)
  simp_rw [hI] at hs
  rw [integral_indicator (s := D) (Series.Radial.disc_meas ..),
    integral_indicator (s := A) isOpen_ball.measurableSet] at hs
  exact hs.symm

theorem analytic_jacobian (G : Gauge) (n : Side) :
    AnalyticAt ℝ (Chart.jacobian (XSpace.Bare.chart G) : Directions G n → ℝ) 0 :=
  (Chart.Ratio.jacobian_smooth (U := Edge (Site n)) (XSpace.Bare.chart_ratio G)).analyticAt

end YM.Integration.WilsonLimitConstruction.FundedWilsonHaar
end
