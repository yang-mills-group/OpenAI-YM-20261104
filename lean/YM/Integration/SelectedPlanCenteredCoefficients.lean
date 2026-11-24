import YM.Integration.FullQLocalNumericStepData

/-!
Center the full output action at the zero external field. This removes only
the field-independent scalar already stored by WholeAction. It preserves
the given model, input, Chain, cutoff and period. Two outputs for exactly
the same input have identical centered coefficients, even if their layer
lists and Plan records differ. No coefficient-size or prediction bound is
asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.SelectedPlan

open Lattice Wilson RG Marker
open Comparison.RG02
open LocalComparison LocalComparison.Global
open scoped BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}
    {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C R}
    {caps caps' : Handoff.OutputCapacities}
    {Y : Bulk.Chain C.path} {K K' : NumericPrices A}
    {F : AnalyticInput J A datum}

/-- The normalized action coefficient with its zero-field value removed. -/
def centeredCoefficient (M : AnalyticOutput caps Y K F)
    (B : Exterior.fieldDir G (C.side datum.level datum.period) 1)
    (k : ℕ) : ℂ :=
  ((k.factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ k (fun g : ℝ => M.whole_action.extension g B) 0
        (fun _ => 1) -
    ((k.factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ k (fun g : ℝ => M.whole_action.extension g 0) 0
        (fun _ => 1)

/-- Exact centered prescription for the original selected output. -/
theorem centered_eq_ground (M : AnalyticOutput caps Y K F)
    (x : TestSpace J.tests)
    (B : Exterior.fieldDir G (C.side datum.level datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) :
    centeredCoefficient M B k =
      Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag
        (F.colors x) J.order k B -
      Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag
        (F.colors x) J.order k 0 := by
  unfold centeredCoefficient
  rw [M.whole_action.output_whole x B k hk,
    M.whole_action.output_whole x 0 k hk]
  abel

/-- Comparison uses the same input and Chain, and does not replace either
Plan or assert equality of their uncentered scalar conventions. -/
theorem centered_eq (M : AnalyticOutput caps Y K F)
    (M' : AnalyticOutput caps' Y K' F) (x : TestSpace J.tests)
    (B : Exterior.fieldDir G (C.side datum.level datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) :
    centeredCoefficient M B k = centeredCoefficient M' B k := by
  exact (centered_eq_ground M x B k hk).trans
    (centered_eq_ground M' x B k hk).symm

end YM.Integration.FullQLocal.RenderedStep.Numeric.SelectedPlan
end
