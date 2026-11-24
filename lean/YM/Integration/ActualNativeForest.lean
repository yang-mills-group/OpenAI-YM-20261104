import YM.Integration.FullQLocalNumericStepData
import YM.RG08.Line.Recipe
import YM.Comparison.RG02.Laplace.Choice

/-!
# The same selected model at a canonical native forest

The native normalized Fk is independent of the physical forest. At positive
orders the ground coefficient is exactly its log-vacuum coefficient, so the
same selected output's whole-action identity can use the canonical green
forest. The order-zero scalar term is not discarded. No model, input, path,
period, or price is selected or changed here.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualNativeForest
open Filter Lattice Wilson RG Precision Tree Marker
open Comparison.RG02 FullQLocal FullQLocal.RenderedStep
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}
    {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G}

/-- The positive-order ground keeps the entire normalized Fk. -/
theorem ground_eq (K : Bulk.Kernel S p P O) (D : BudgetPoint)
    (F H : Forest S.ratio) (t : S.Choices) (W : Bulk.Colors R G f)
    (hW : Bulk.Well W) (r k : ℕ) (hk : k ≠ 0)
    (B : Exterior.fieldDir G c 1) :
    Symmetry.Orbit.ground K F t W r k B =
      Symmetry.Orbit.ground K H t W r k B := by
  have he := (Laplace.identical K F H t 0 W B D r hW).2
  simp only [Symmetry.Orbit.ground, if_neg hk, add_zero]
  rw [he]

variable {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C R} {caps : Handoff.OutputCapacities}
    {Y : Bulk.Chain C.path} {K : NumericPrices A}
    {F : Numeric.AnalyticInput J A datum}

/-- This is the original selected output's identity, with no new selector. -/
theorem output_whole (M : Numeric.AnalyticOutput caps Y K F)
    (x : LocalComparison.TestSpace J.tests)
    (B : Exterior.fieldDir G (C.side datum.level datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) (hpositive : k ≠ 0) :
    ((k.factorial : ℝ)⁻¹) •
      iteratedFDeriv ℝ k (fun g : ℝ => M.whole_action.extension g B) 0
        (fun _ => 1) =
      Symmetry.Orbit.ground (datum.kernel Y)
        (RG08.Line.green (C.path.levels.clock.op datum.level datum.period))
        datum.tag (F.colors x) J.order k B + M.whole_action.scalar k := by
  rw [M.whole_action.output_whole x B k hk]
  rw [ground_eq (datum.kernel Y)
    (C.path.levels.budget (datum.level + 1)) datum.forest
    (RG08.Line.green (C.path.levels.clock.op datum.level datum.period))
    datum.tag (F.colors x) (F.whole_input.standard x).1 J.order k hpositive B]

end YM.Integration.ActualNativeForest
end
