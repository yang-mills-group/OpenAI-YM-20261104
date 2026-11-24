import YM.Integration.ZeroAwareVacuumPackets

/-!
# Grading of the unchanged vacuum layer list

This is a data class for the leading curvature rank and coupling degree of
each additional packet. The full nonlinear completion stays in the same
atom/action fields. A bound on leading rank is not a bound on the Taylor
degree of that nonlinear completion.

The class retains the true per-root exponential costs and every original
row, including zero rows. Its three elementary consequences only expose
the nonnegative cleared coupling power and the leading degree. Joint
analyticity, the canonical formal prescription, the actual reset, and the
qlocal estimate require their separate proofs. No existing target is changed.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal

open Lattice Wilson RG
open IterationFour.Vacuum

structure GradedVacuumLayers {G : Gauge} {n : Side}
    (layers : List (Piece G n)) (p : BudgetPoint)
    (order rankCap : ℕ) (width budget : ℝ) where
  packets : LocalComparison.Global.ZeroAwareVacuumPackets
    layers p rankCap width budget
  orders : Render.gradings layers order
  leading_rank a : a ∈ layers → a.rank ≤ a.power + 2

namespace GradedVacuumLayers

variable {G : Gauge} {n : Side} {layers : List (Piece G n)}
    {p : BudgetPoint} {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers layers p order rankCap width budget)
    {a : Piece G n} (ha : a ∈ layers)

include H ha in
/-- Clearing the two inverse coupling powers leaves a nonnegative exponent. -/
theorem cleared_nonnegative : 0 ≤ (a.power : ℤ) - (a.rank : ℤ) + 2 := by
  have hr := H.leading_rank a ha
  omega

include H ha in
/-- This concerns the leading joint degree of an additional packet. -/
theorem leading_degree : 5 ≤ a.power + 2 := by
  have hp := (H.orders a ha).1
  omega

include H ha in
/-- The finite output rank capacity may be derived from the requested order. -/
theorem rank_le_order : a.rank ≤ order + 2 := by
  have hr := H.leading_rank a ha
  have hp := (H.orders a ha).2
  omega

end GradedVacuumLayers
end YM.Integration.FullQLocal

end
