import YM.Integration.SelectedPlanTriangular
import YM.Integration.ActualNativeForest

/-! The selected model's next coefficient is determined by its original ground
coefficient and the exact same-list numerator with earlier coefficients.
The green-forest form changes no model, Plan, input, scalar, or field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanGroundTriangle
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} (T : Run G)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J}
    {datum : LocalFormal.Datum T.family R}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain T.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}

def priorCentered (M : AnalyticOutput caps Y K F) (e : ℕ)
    (B : fieldDir G (T.family.side datum.level datum.period) 1) : ℂ :=
  jet (SelectedPlanClearedNumerator.numerator T
    (SelectedPlanTriangular.prior M.plan e) datum.level) (e + 4) (1, B) -
  jet (SelectedPlanClearedNumerator.numerator T
    (SelectedPlanTriangular.prior M.plan e) datum.level) (e + 4) (1, 0)

/-- Exact triangular identity for the same selected model, before any bounds. -/
theorem coefficient (M : AnalyticOutput caps Y K F)
    (x : TestSpace J.tests) (e : ℕ) (he : e ≤ J.order - 2)
    (B : fieldDir G (T.family.side datum.level datum.period) 1) :
    ((M.plan.coefficient datum.level e *
        jet (SelectedPlanTriangular.kinetic (N := datum.cutoff)
          (period := datum.period) T datum.level) 2 B : ℝ) : ℂ) =
      Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag
          (F.colors x) J.order (e + 2) B -
        Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag
          (F.colors x) J.order (e + 2) 0 - priorCentered T M e B := by
  have hB := SelectedPlanTriangular.coefficient T M.plan datum.level M.vacuum
    e he datum.below.le (A.output_width_pos datum.level) B
  have h0 := SelectedPlanTriangular.coefficient T M.plan datum.level M.vacuum
    e he datum.below.le (A.output_width_pos datum.level) 0
  have hz : jet (SelectedPlanTriangular.kinetic (N := datum.cutoff)
      (period := datum.period) T datum.level) 2 0 = 0 := by
    unfold jet
    rw [(iteratedFDeriv ℝ 2 (SelectedPlanTriangular.kinetic (N := datum.cutoff)
      (period := datum.period) T datum.level) 0).map_coord_zero (0 : Fin 2) rfl, smul_zero]
  rw [hz, mul_zero, Complex.ofReal_zero, sub_eq_zero] at h0
  have hk : e + 2 ≤ J.order := by
    have := J.order_ge_two
    omega
  have hwhole := SelectedPlanClearedNumerator.centered_ground T M x B (e + 2) hk
  have hdegree : 2 + (e + 2) = e + 4 := by omega
  rw [hdegree] at hwhole
  rw [← hB, ← hwhole]
  unfold priorCentered
  rw [h0]
  abel

/-- The same positive-order identity in the native paid forest. -/
theorem coefficient_green (M : AnalyticOutput caps Y K F)
    (x : TestSpace J.tests) (e : ℕ) (he : e ≤ J.order - 2)
    (B : fieldDir G (T.family.side datum.level datum.period) 1) :
    ((M.plan.coefficient datum.level e *
        jet (SelectedPlanTriangular.kinetic (N := datum.cutoff)
          (period := datum.period) T datum.level) 2 B : ℝ) : ℂ) =
      Symmetry.Orbit.ground (datum.kernel Y)
          (RG08.Line.green (T.family.path.levels.clock.op datum.level datum.period))
          datum.tag (F.colors x) J.order (e + 2) B -
        Symmetry.Orbit.ground (datum.kernel Y)
          (RG08.Line.green (T.family.path.levels.clock.op datum.level datum.period))
          datum.tag (F.colors x) J.order (e + 2) 0 - priorCentered T M e B := by
  rw [coefficient T M x e he B]
  rw [ActualNativeForest.ground_eq (datum.kernel Y)
    (T.family.path.levels.budget (datum.level + 1)) datum.forest
    (RG08.Line.green (T.family.path.levels.clock.op datum.level datum.period))
    datum.tag (F.colors x) (F.whole_input.standard x).1 J.order (e + 2) (by omega) B]
  rw [ActualNativeForest.ground_eq (datum.kernel Y)
    (T.family.path.levels.budget (datum.level + 1)) datum.forest
    (RG08.Line.green (T.family.path.levels.clock.op datum.level datum.period))
    datum.tag (F.colors x) (F.whole_input.standard x).1 J.order (e + 2) (by omega) 0]

end YM.Integration.SelectedPlanGroundTriangle
end
