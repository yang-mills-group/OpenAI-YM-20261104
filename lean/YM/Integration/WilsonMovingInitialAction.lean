import YM.Integration.WilsonMovingVacuumRows
import YM.MSbar.Rolling.Sprout
import YM.MSbar.Rolling.Arc

/-! The actual prepared UV bank is the genuinely independently booked bare
vacuum with its Gaussian quadratic removed. At any later date the original
Jacobian and true block kernel cancel in the signed primitive difference for
two incoming vacua on the same forest, before it is exponentiated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingInitialAction
open PowerSeries Lattice Exterior Wilson Precision RG Push.Uniform Tree MSbar.Rolling
open scoped Classical

theorem original (G : Gauge) (n : Side) :
    MSbar.Rolling.opening G n = WilsonMovingBareVacuum.released G n := by
  rw [opening, splitV, WilsonMovingBareVacuum.released, WilsonMovingVacuumRows.bare]
  change -(_ - C (coeff 0 _)) =
    -singularity (WilsonMovingBareVacuum.energy G n) 2 -
      C (coeff 0 (-singularity (WilsonMovingBareVacuum.energy G n) 2))
  rw [map_neg, map_neg]
  abel

theorem transported {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)
    (t : S.Choices) (O : ChartRatio G) (P Q : PowerSeries (MvPolynomial (Primary f G) ℝ)) :
    MSbar.Rolling.barbed F t O P - MSbar.Rolling.barbed F t O Q =
      PowerSeries.map (rail (taps F G)).toRingHom (P-Q) := by
  rw [map_sub]
  unfold MSbar.Rolling.barbed
  abel

theorem inserted {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)
    (t : S.Choices) (O : ChartRatio G) :
    MSbar.Rolling.barbed F t O (MSbar.Rolling.opening G f) =
      MSbar.Rolling.barbed F t O (WilsonMovingBareVacuum.released G f) := by
  rw [original]

end YM.Integration.WilsonMovingInitialAction
end
