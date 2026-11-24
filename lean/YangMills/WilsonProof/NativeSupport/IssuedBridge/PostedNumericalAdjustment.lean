import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAdjustmentExpansion
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAdjustmentGrades
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAdjustmentSymmetries
import MSNumericalAdjustment
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedNumericalAdjustment
open YangMills YangMills.Wilson YM YM.Integration YM.Maxwell YM.Maxwell.Free WilsonLimitConstruction
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale MS MS.Land
open WilsonPositionHomogeneousCoefficients

/-- The smooth representative on the original prescription, chosen before the physical hierarchy. -/
def filed {g : GaugeGroup} (Z : WilsonPrescription g.core) (law : Warrant Z) :
    YangMills.MSbar.NumericalAdjustment (maxwellReference g)
      (fun d k => PowerSeries.coeff k (Measure.adjust Z.scheme Z.criterion d)) where
  value := PostedBilateralAdjustment.value Z
  at_zero := PostedBilateralAdjustment.zero Z
  smooth := PostedBilateralAdjustment.original Z
  invertible := PostedAdjustmentFields.invertible Z
  unit := fun t _ => PostedAdjustmentFields.unit Z t
  nested := fun _ ht => PostedAdjustmentFields.original Z law ht
  triangular := fun _ ht => PostedAdjustmentGrades.original Z law ht
  real := fun t _ d => PostedAdjustmentSymmetries.real Z d t
  signedAxes := fun t _ => PostedAdjustmentSymmetries.original Z t
  expansion := PostedAdjustmentExpansion.original Z law

theorem original {g : GaugeGroup} (Z : WilsonPrescription g.core) (law : Warrant Z) (d : ℕ)
    {t : ℝ} (ht : 0 < t) :
    (filed Z law).value d t = stand (WilsonPositionHomogeneousRealization.correction Z d t) :=
  congrArg stand (PostedBilateralAdjustment.positive Z d ht)
end IssuedBridge.PostedNumericalAdjustment
