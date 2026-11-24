import YM.Integration.WilsonPositionProgramMeasuredFieldShift

/-! The original inverse angular arm is a contraction on every finite side and every link sector. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramAngularArm
open Lattice Exterior Laurent
open scoped Classical ENNReal

theorem original (G:Gauge)(side:Side)(r:ℕ):
    ‖(Stationary.arm G side r).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2
  intro e
  exact (PiLp.norm_apply_le (u (e.1,e.2.1)) e.2.2).trans (norm_le_pi_norm u (e.1,e.2.1))

end YM.Integration.WilsonPositionProgramAngularArm
end
