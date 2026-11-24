import YM.Integration.WilsonGraphAppointedWardGroundRhs
import YM.Integration.WilsonGraphAppointedWardTranslationIntegral

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonGraphAppointedWardTranslationRow

open _root_.YangMills _root_.YangMills.Matching
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils)
open _root_.PhysicalMatching.H7StandaloneTranslationTestSupport (weight)
open _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients (groupMarked fluxEntry rhsCoefficients)
open MeasureTheory
open scoped BigOperators Classical

variable {g : GaugeGroup} {H : g.core.Simple}
  (Z : _root_.YM.FVA2.Register.WilsonPrescription g.core)
  (Q : _root_.YM.Answer.ContinuumLimit.Perspective H Z true)

theorem directionAt (P : Pupils) (a : Axis) (z : Spacetime × Points 2) :
    weight P a z * groupMarked Z Q 0 a 0 3 (fun _ : Fin 2 => 0) (Ward.prepend z.1 z.2) =
      WilsonGraphAppointedWardTranslationIntegral.direction H P a z := by
  by_cases hz : weight P a z = 0
  · simp [WilsonGraphAppointedWardTranslationIntegral.direction, hz]
  · have hx := _root_.PhysicalMatching.H7StandaloneTranslationTestSupport.separated P a
        (subset_tsupport _ hz)
    rw [WilsonGraphAppointedWardGroundMatrix.marked Z Q a 3 (fun _ : Fin 2 => 0) _ hx]
    unfold WilsonGraphWardGroundMatrix.reading
    rw [_root_.PhysicalMatching.H7IndependentGroupFirstWardTree.groupLeading _ _ _ hx]
    unfold WilsonGraphAppointedWardTranslationIntegral.direction
    apply congrArg (fun v => weight P a z * (maxwellReference g).moment (Ward.prepend z.1 z.2) v)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem atPupils (P : Pupils) :
    fluxEntry Z Q P 0 3 = rhsCoefficients Z Q P 0 3 := by
  calc
    _ = -(∑ a : Axis, ∫ z : Spacetime × Points 2,
          WilsonGraphAppointedWardTranslationIntegral.direction H P a z) := by
      unfold fluxEntry
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro a _
      apply integral_congr_ae
      filter_upwards [] with z
      exact directionAt Z Q P a z
    _ = WilsonGraphAppointedWardGroundRhs.maxwellRhs H P 3 :=
      WilsonGraphAppointedWardTranslationIntegral.ground H P
    _ = _ := (congrFun (WilsonGraphAppointedWardGroundRhs.atPupils Z Q P) 3).symm

end YM.Integration.WilsonGraphAppointedWardTranslationRow
end

