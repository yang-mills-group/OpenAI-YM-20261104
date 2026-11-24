import YM.Integration.ActualStartupPaidPhysical
import YM.Integration.FullQLocalNumericSchedule

/-! The original top physical exponent at the exact requested input norm.
The threshold and minimum-order conditions are supplied by the numerical
schedule and Request themselves. The complete original chip is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRequestedStartupPhysical
open Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum FullQLocal.RenderedStep

variable {G : Gauge} {V : Type} (R : Run G)
    (J : Request V) (A : NumericSchedule R.family J)

/-- The requested norm has the original top representation's threshold. -/
theorem threshold (m period : ℕ) :
    (A.inputNorm m).threshold =
      (R.family.path.rep (m + 1) period (m + 1)).p.threshold :=
  (A.input_norm m).threshold.trans
    (congrArg BudgetPoint.threshold
      (R.makes.wilson.represents (m + 1) period (m + 1) le_rfl).vac).symm

def calibration (m period : ℕ) :=
  ActualStartupCalibration.calibration R (m + 1) period (A.inputNorm m)
    (threshold R J A m period)

/-- The actual top carrier, original beta, paid album and complete chip
satisfy the exact physical equality at every field configuration. -/
theorem physical_exponent (T : Campaign R) (m period : ℕ)
    (U : Config G (R.family.side (m + 1) period)) :
    let X := R.family.path.rep (m + 1) period (m + 1)
    X.exponent U = X.scalar -
      (X.path.inChannels X.clip X.p
        (R.family.path.β (m + 1) period (m + 1)) U +
        Render.renders
          (Render.prefactor
            (Pert.Asymptotics.regulatorRun R.family (m + 1) period (m + 1)))
          X.p U
          (ActualStartupInvoice.paidAlbum G (R.family.side (m + 1) period)
            (A.inputNorm m) (R.family.path.levels.params (m + 1))
            J.order (A.inputWidth m))) -
      (ActualStartupMaskedAction.remainder R (m + 1) period J.order).amount
        (A.inputNorm m) U - (calibration R J A m period).amount U :=
  ActualStartupPaidPhysical.physical_exponent R T (m + 1) period J.order
    J.order_ge_two (A.inputNorm m) (threshold R J A m period) (A.inputWidth m) U

end YM.Integration.ActualRequestedStartupPhysical
end
