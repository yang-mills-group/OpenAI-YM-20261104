import YM.Integration.ActualStartupCalibration
import YM.Integration.ActualStartupInvoice

/-!
The original top physical exponent after credit-only repricing of its
unchanged startup album. The complete chip remains in the inherited error
and the original zero calibration remains explicit.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupPaidPhysical
open Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open YM.IterationFour YM.IterationFour.Vacuum

variable {G : Gauge}

/-- The paid album uses the requested derivative norm while the original
top representation, masking threshold, physical exponent and full chip
remain literal. This is not a later-reset zero-calibration claim. -/
theorem physical_exponent (R : Run G) (T : Campaign R) (N p r : ℕ)
    (hr : 2 ≤ r) (Q : BudgetPoint)
    (hQ : Q.threshold = (R.family.path.rep N p N).p.threshold)
    (width : ℝ) (U : Config G (R.family.side N p)) :
    let X := R.family.path.rep N p N
    X.exponent U = X.scalar -
      (X.path.inChannels X.clip X.p X.beta U +
        Render.renders
          (Render.prefactor (Pert.Asymptotics.regulatorRun R.family N p N))
          X.p U (ActualStartupInvoice.paidAlbum G (R.family.side N p) Q
            (R.family.path.levels.params N) r width)) -
      (ActualStartupMaskedAction.remainder R N p r).amount Q U -
      (ActualStartupCalibration.calibration R N p Q hQ).amount U := by
  dsimp only
  rw [ActualStartupInvoice.paid_from_original G _ (R.family.path.rep N p N).p Q
      (R.family.path.levels.params N) r width,
    ActualStartupInvoice.reprice_renders]
  exact ActualStartupCalibration.physical_exponent R T N p r hr Q hQ U

end YM.Integration.ActualStartupPaidPhysical
end
