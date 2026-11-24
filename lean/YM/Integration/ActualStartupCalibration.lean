import YM.Integration.ActualStartupMaskedAction
import YM.Integration.LocalComparisonCalibrationClass

/-! The optional startup calibration is literally zero because the complete
original chip payload remains in the inherited error. This is an exact
all-field identity on the original top representation; it does not construct
an AnalyticDatum or assert any zero correction after a later reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStartupCalibration

open Lattice Wilson RG MeasureTheory
open PhysicalNext.Repeat.Legato
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open YM.IterationFour YM.IterationFour.Vacuum
open scoped Classical BigOperators

variable {G : Gauge} {n : Side}

private theorem zero_jet (l : List (Directions G n)) (U : Config G n) :
    leftDerivs (0 : Config G n → ℝ) l U = 0 := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp only [leftDerivs, ih, deriv_const]

private theorem zero_regular (Q : BudgetPoint) (s : Support n) :
    Q.Regular s (0 : Config G n → ℝ) where
  sites _ _ _ := rfl
  borel := measurable_const
  symmetry _ _ := rfl
  smooth _ _ := contDiffAt_const
  hasDerivs U _ A l _ := by
    have he : (fun t : ℝ => leftDerivs (0 : Config G n → ℝ) l
        (increment U (t • A))) = fun _ => 0 := funext fun _ => zero_jet _ _
    rw [he, zero_jet]
    exact hasDerivAt_const 0 0

/-- Zero values on the original regular address inventory. No address,
activity, clipping rule, or gas in the original representation is changed. -/
def calibration (R : Run G) (N p : ℕ) (Q : BudgetPoint)
    (hQ : Q.threshold = (R.family.path.rep N p N).p.threshold) :
    FullQLocal.CalibrationPresentation (R.family.path.rep N p N) Q 0 where
  threshold := hQ
  size_nonnegative := le_rfl
  address := (R.family.path.rep N p N).activities.reg
  original _ := 0
  germ _ := 0
  regular _ := zero_regular Q _
  original_measurable _ := measurable_const
  original_gauge _ _ _ := rfl
  original_reads _ _ _ _ _ := rfl
  on_healthy _ _ _ := rfl
  regularMajorant _ := 0
  fullMajorant _ := 0
  regular_bound _ := ⟨le_rfl, fun U _ l _ _ => by rw [zero_jet, norm_zero]⟩
  full_nonnegative _ := le_rfl
  original_bound _ _ := by simp only [Pi.zero_apply, norm_zero, le_refl]
  germ_bound _ _ := by simp only [Pi.zero_apply, norm_zero, le_refl]
  regular_total _ := by simp [SumBudget, BudgetPoint.mass]
  full_hit _ := by simp [SumBudget, BudgetPoint.mass]

theorem calibration_amount (R : Run G) (N p : ℕ) (Q : BudgetPoint)
    (hQ : Q.threshold = (R.family.path.rep N p N).p.threshold)
    (U : Config G (R.family.side N p)) :
    (calibration R N p Q hQ).amount U = 0 := by
  simp only [FullQLocal.CalibrationPresentation.amount, calibration,
    Pi.zero_apply, tsum_zero]

/-- Exact startup physical exponent at any requested norm with the same
threshold. The full original chip is retained as the inherited error. -/
theorem physical_exponent (R : Run G) (T : Campaign R) (N p r : ℕ)
    (hr : 2 ≤ r) (Q : BudgetPoint)
    (hQ : Q.threshold = (R.family.path.rep N p N).p.threshold)
    (U : Config G (R.family.side N p)) :
    let X := R.family.path.rep N p N
    X.exponent U = X.scalar -
      (X.path.inChannels X.clip X.p X.beta U +
        Render.renders
          (Render.prefactor (Pert.Asymptotics.regulatorRun R.family N p N))
          X.p U (album G (R.family.side N p) X.p
            (R.family.path.levels.params N) r)) -
      (ActualStartupMaskedAction.remainder R N p r).amount Q U -
      (calibration R N p Q hQ).amount U := by
  dsimp only
  rw [calibration_amount, sub_zero]
  have he : (ActualStartupMaskedAction.remainder R N p r).amount Q U =
      (ActualStartupMaskedAction.remainder R N p r).amount
        (R.family.path.rep N p N).p U := by
    simp only [Payload.amount, hQ]
  rw [he]
  exact ActualStartupMaskedAction.exponent R T N p r hr U

end YM.Integration.ActualStartupCalibration
end
