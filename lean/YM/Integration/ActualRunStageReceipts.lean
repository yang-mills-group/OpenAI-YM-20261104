import YM.Integration.ActualRunStageStepCore

/-! Native receipts retained before the original construction forgets them. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato

/-- These are already-paid inputs on one literal Run, including its exact
support and paced clock. This structure makes no new construction choice. -/
structure StageReceipts {G : Gauge} (R : Run G) : Prop where
  marker : Mallow.RG12.Earned
    (ConnectedActivityE6.Blaze.Thermal1020.Shared.markerBudget G)
    R.kit.shape R.alloy.delay
  garrison : Mallow.RG12.Earned (PhysicalNext.Repeat.FVA1.garrison G)
    R.kit.shape R.alloy.delay
  support : ∀ i, 100 ≤ (R.alloy.B.a.budget i).supportExponent
  paced : ∀ i, ((R.family.S.block i).val : ℝ) ≤
    Real.log (R.family.path.levels.clock.hatBeta i)

end YM.Integration
