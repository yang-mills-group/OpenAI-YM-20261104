import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellIntegrationByParts
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentGroupMaxwellIntegrability
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTranslationTestSupport
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonGraphAppointedWardTranslationIntegral

open YM YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick
open MeasureTheory
open PhysicalMatching.H7StandaloneFourSmearedWardReadings
open PhysicalMatching.H7IndependentFiledMaxwellIntegrationByParts
open PhysicalMatching.H7IndependentGroupMaxwellIntegrability
open scoped BigOperators Classical

variable {g : YangMills.GaugeGroup}

def direction (H : g.core.Simple) (P : Pupils) (a : Axis)
    (z : YangMills.Spacetime × Points 2) : ℂ :=
  PhysicalMatching.H7StandaloneTranslationTestSupport.weight P a z *
    moment g.core (YangMills.Ward.prepend z.1 z.2)
      (Fin.cons (-polStress g.core a 0) (actualProbes H))

theorem integrable (H : g.core.Simple) (P : Pupils) (a : Axis) :
    Integrable (direction H P a) :=
  signedShellMomentIntegrable (Fin.cons (-polStress g.core a 0) (actualProbes H))
    (PhysicalMatching.H7StandaloneTranslationTestSupport.weight P a)
    (PhysicalMatching.H7StandaloneTranslationTestSupport.smoothWeight P a)
    (PhysicalMatching.H7StandaloneTranslationTestSupport.compact P a)
    (fun _ hz => PhysicalMatching.H7StandaloneTranslationTestSupport.separated P a hz)

theorem nested (H : g.core.Simple) (P : Pupils) :
    -(∑ a : Axis, ∫ z : YangMills.Spacetime × Points 2, direction H P a z) =
      ∫ x : Points 2, P.translation x *
        exportFlux (fun a y => bookend x y (actualProbes H) (-polStress g.core a 0))
          P.cutoff := by
  calc
    _ = -(∑ a : Axis, ∫ x : Points 2, ∫ y : YangMills.Spacetime,
          direction H P a (y, x)) := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro a _
      exact integral_prod_symm _ (integrable H P a)
    _ = ∫ x : Points 2, -(∑ a : Axis, ∫ y : YangMills.Spacetime,
          direction H P a (y, x)) := by
      rw [integral_neg, integral_finsetSum _ (fun a _ => (integrable H P a).integral_prod_right)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [exportFlux, mul_neg, Finset.mul_sum]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro a _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [book_eval, Algebra.smul_def]
      exact mul_assoc _ _ _

theorem ground (H : g.core.Simple) (P : Pupils) :
    -(∑ a : Axis, ∫ z : YangMills.Spacetime × Points 2, direction H P a z) =
      -(∫ x : Points 2, Points.gradient 0 0 (fun z => P.translation z) x *
        moment g.core x (actualProbes H)) :=
  (nested H P).trans (originalPupil H P)

end YM.Integration.WilsonGraphAppointedWardTranslationIntegral
