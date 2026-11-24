import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import MSConversion
import YangMills.WilsonProof.NativeSupport.MSFormalSeries
import MSPositionFrame
import MSPositionPrescription
import MSPositionScreens
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.MSPositionLabels
import MSScalarReverse
import MSScalarInverse
import MSNumericalAdjustment
import YM.XSpace.Panorama

/-! The position tests and the coupling and field conversions are fixed before any
lattice family is selected. The smooth realization below fixes the numerical field
change, including terms invisible to its Taylor series. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.CorrelationMatching

open YM.XSpace.Normalize
open scoped BigOperators Classical

/-- A common choice of finite position tests, formal conversion and numerical field
change for all refinements of one gauge group. -/
structure Normalization (g : GaugeGroup) where
  prescription : MSbar.PositionPrescription (maxwellReference g)
  conversion : MSbar.PositionConversion (maxwellReference g)
  adjustment : MSbar.NumericalAdjustment (maxwellReference g) conversion.adjustment

private def correctionCoordinates (g : GaugeGroup)
    (conversion : MSbar.PositionConversion (maxwellReference g)) (d n : ℕ) : MoveSpace g.core d :=
  guide g.core d (if n = 0 then 0
    else if permitted : conversion.adjustment d n ∈ Change g.core d
      then ⟨conversion.adjustment d n, permitted⟩ else 0)

private def cutoffWidth {g : GaugeGroup} (a : (d : ℕ) → ℕ → MoveSpace g.core d) (n : ℕ) : ℝ :=
  let size (d : ℕ) := 1 + ∑ j ∈ Finset.range (d + 1), ‖a d j‖
  let cap := 1 + ∑ d ∈ Finset.range (n + 1), ‖(size d)⁻¹ • a d n‖
  2 ^ (n + 1) * (1 + cap) + (n : ℝ) + 1

/-- Realize each positive-order field correction with the same smooth cutoff across
grades. The two transition factors give a smooth function on both sides of zero. -/
def smoothAdjustment (g : GaugeGroup) (conversion : MSbar.PositionConversion (maxwellReference g))
    (d : ℕ) (t : ℝ) : Module.End ℂ ((maxwellReference g).sector d) :=
  let a := correctionCoordinates g conversion
  let weight (n : ℕ) :=
    let width := cutoffWidth (g := g) a n
    Real.smoothTransition (2 + width * t) * (Real.smoothTransition (2 - width * t) * t ^ n)
  stand ((guide g.core d).symm (∑' n : ℕ, weight n • a d n))

/-- The substantive calibration equations at an externally specified menu. -/
structure CalibrationAt (g : GaugeGroup) (M : MSbar.Coefficients (maxwellReference g))
    (menu : MSbar.PositionPrescription (maxwellReference g)) (N : Normalization g) : Prop where
  prescription : N.prescription = menu
  admissible : MSbar.Admissible menu
  signedSlope (triangle : MSbar.Position.Triangle (maxwellReference g)) :
    triangle.Admissible → triangle.RawSlopeAgrees M
  conversionValid : MSbar.ConversionValid M menu N.conversion
  adjustmentValue (d : ℕ) (t : ℝ) : N.adjustment.value d t = smoothAdjustment g N.conversion d t

/-- The reference menu is fixed from the gauge group before any normalization or
Wilson family is supplied. The choice of admissible test profiles is classical. -/
def groupMenu (g : GaugeGroup) : Option (MSbar.PositionPrescription (maxwellReference g)) :=
  if available : Nonempty {P : MSbar.PositionPrescription (maxwellReference g) // MSbar.Admissible P}
  then some (MSbar.nominatedMenu available).val else none

/-- Calibration at the published menu also identifies the group nomination. -/
structure CalibrationLaws (g : GaugeGroup) (M : MSbar.Coefficients (maxwellReference g))
    (N : Normalization g) : Prop extends CalibrationAt g M N.prescription N where
  nominated : some N.prescription = groupMenu g

private theorem numericalAdjustment_ext {g : GaugeGroup}
    {conversion : MSbar.PositionConversion (maxwellReference g)}
    {A B : MSbar.NumericalAdjustment (maxwellReference g) conversion.adjustment}
    (same : A.value = B.value) : A = B := by
  cases A
  cases B
  cases same
  rfl

/-- For any specified menu, the equations determine at most one normalization. -/
theorem calibration_unique_at {g : GaugeGroup} {M : MSbar.Coefficients (maxwellReference g)}
    {menu : MSbar.PositionPrescription (maxwellReference g)} {N P : Normalization g}
    (hN : CalibrationAt g M menu N) (hP : CalibrationAt g M menu P) : N = P := by
  obtain ⟨menuN, conversion, adjustment⟩ := N
  obtain ⟨menuP, conversion', adjustment'⟩ := P
  have h1 : menuN = menu := hN.prescription
  have h2 : menuP = menu := hP.prescription
  subst menuN
  subst menuP
  have sameConversion : conversion = conversion' :=
    MSbar.conversionValid_unique hN.conversionValid hP.conversionValid
  subst conversion'
  have sameValue : adjustment.value = adjustment'.value :=
    funext fun d => funext fun t => (hN.adjustmentValue d t).trans (hP.adjustmentValue d t).symm
  have sameAdjustment := numericalAdjustment_ext (conversion := conversion) sameValue
  cases sameAdjustment
  rfl

/-- For the published nomination, relative uniqueness specializes to the group result. -/
theorem calibration_unique {g : GaugeGroup} {M : MSbar.Coefficients (maxwellReference g)}
    {N P : Normalization g} (hN : CalibrationLaws g M N) (hP : CalibrationLaws g M P) : N = P := by
  have sameMenu : P.prescription = N.prescription := Option.some.inj (hP.nominated.trans hN.nominated.symm)
  exact calibration_unique_at hN.toCalibrationAt (sameMenu ▸ hP.toCalibrationAt)

end YangMills.CorrelationMatching
