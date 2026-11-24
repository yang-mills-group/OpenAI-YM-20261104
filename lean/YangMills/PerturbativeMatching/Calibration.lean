import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import YangMills.MaxwellReference
import MSConversion
import MSNumericalAdjustment
import MSPositionPrescription
import YM.XSpace.Influence

/-! The position tests and the coupling and field conversions are fixed before any
lattice family is selected. The smooth realization below fixes the numerical field
change, including terms invisible to its Taylor series. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.PerturbativeMatching

open YM.XSpace.Normalize
open scoped BigOperators Classical

/-- A common choice of finite position tests, formal conversion and numerical field
change for all refinements of one gauge group. -/
structure PositionScheme (g : GaugeGroup) where
  prescription : MSbar.PositionPrescription (maxwellReference g)
  series : MSbar.PositionConversion (maxwellReference g)
  adjustment : MSbar.NumericalAdjustment (maxwellReference g) series.adjustment

/-- Formal substitution of the coupling and external fields. -/
abbrev PositionScheme.conversion {g : GaugeGroup} (scheme : PositionScheme g) :=
  scheme.series.conversion

private abbrev CorrectionSpace (G : YM.Gauge) (d : ℕ) :=
  Fin (Module.finrank ℝ (Change G d)) → ℝ

private def correctionBasis (G : YM.Gauge) (d : ℕ) :=
  (Module.finBasis ℝ (Change G d)).equivFun

private def correctionCoordinates (g : GaugeGroup)
    (conversion : MSbar.PositionConversion (maxwellReference g)) (d n : ℕ) : CorrectionSpace g.core d :=
  correctionBasis g.core d (if n = 0 then 0
    else if permitted : conversion.adjustment d n ∈ Change g.core d
      then ⟨conversion.adjustment d n, permitted⟩ else 0)

private def cutoffWidth {g : GaugeGroup} (a : (d : ℕ) → ℕ → CorrectionSpace g.core d) (n : ℕ) : ℝ :=
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
  (1 : Module.End ℂ (Sec g.core d)) + ((correctionBasis g.core d).symm (∑' n : ℕ, weight n • a d n)).val

/-- The reference menu is fixed from the gauge group before any normalization or
Wilson family is supplied. The choice of admissible test profiles is classical. -/
def groupMenu (g : GaugeGroup) : Option (MSbar.PositionPrescription (maxwellReference g)) :=
  if available : Nonempty {P : MSbar.PositionPrescription (maxwellReference g) // MSbar.Admissible P}
  then some (MSbar.nominatedMenu available).val else none

/-- The signed position tests determine the formal and numerical scheme changes. -/
structure Calibration {g : GaugeGroup} (coefficients : MSbar.Coefficients (maxwellReference g))
    (scheme : PositionScheme g) : Prop where
  admissible : MSbar.Admissible scheme.prescription
  signedSlope (triangle : MSbar.Position.Triangle (maxwellReference g)) :
    triangle.Admissible → triangle.RawSlopeAgrees coefficients
  conversionValid : MSbar.ConversionValid coefficients scheme.prescription scheme.series
  adjustmentValue (d : ℕ) (t : ℝ) : scheme.adjustment.value d t = smoothAdjustment g scheme.series d t

private theorem numericalAdjustment_ext {g : GaugeGroup}
    {conversion : MSbar.PositionConversion (maxwellReference g)}
    {A B : MSbar.NumericalAdjustment (maxwellReference g) conversion.adjustment}
    (same : A.value = B.value) : A = B := by
  cases A
  cases B
  cases same
  rfl

/-- At a specified menu the calibration equations determine at most one scheme. -/
theorem Calibration.uniqueAt {g : GaugeGroup} {M : MSbar.Coefficients (maxwellReference g)}
    {left right : PositionScheme g} (hLeft : Calibration M left) (hRight : Calibration M right)
    (sameMenu : left.prescription = right.prescription) : left = right := by
  obtain ⟨menu, series, adjustment⟩ := left
  obtain ⟨otherMenu, otherSeries, otherAdjustment⟩ := right
  change menu = otherMenu at sameMenu
  subst otherMenu
  have sameSeries : series = otherSeries :=
    MSbar.conversionValid_unique hLeft.conversionValid hRight.conversionValid
  subst otherSeries
  have sameValues : adjustment.value = otherAdjustment.value :=
    funext fun d => funext fun t => (hLeft.adjustmentValue d t).trans (hRight.adjustmentValue d t).symm
  cases numericalAdjustment_ext sameValues
  rfl

end YangMills.PerturbativeMatching
