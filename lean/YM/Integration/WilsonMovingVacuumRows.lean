import YM.Integration.WilsonMovingBareVacuum
import YM.MSbar.Rolling.Stays

/-! The moving conditional chart and the independent coefficient construction
have identical factorial and Laurent conventions, at every coupling order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingVacuumRows
open PowerSeries Function Lattice Push.Uniform FormalBulk08 Jets
open scoped Classical BigOperators

theorem homogeneous {I : Type} [Fintype I] (f : Jets.Rays I → ℝ) (n : ℕ) :
    MSbar.Rolling.potter f n = WilsonMovingTaylorConvention.tensor f n := by
  unfold MSbar.Rolling.potter WilsonMovingTaylorConvention.tensor
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

theorem shifted {I : Type} [Fintype I] (f : Jets.Rays I → ℝ) (r : ℕ) :
    MSbar.Rolling.singularity f r = Jets.afterX (Jets.paste f) r := by
  apply PowerSeries.ext
  intro i
  rw [MSbar.Rolling.singularity, coeff_mk, homogeneous, WilsonMovingTaylorConvention.coefficient,
    Jets.after_one, Nat.add_comm]

theorem bare (G : Gauge) (n : Side) :
    WilsonMovingBareVacuum.seed G n =
      -MSbar.Rolling.singularity (WilsonMovingBareVacuum.energy G n) 2 := by
  rw [shifted, WilsonMovingBareVacuum.positions]

end YM.Integration.WilsonMovingVacuumRows
end
