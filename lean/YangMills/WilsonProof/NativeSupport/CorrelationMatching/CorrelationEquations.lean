import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Coefficients
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Normalization
import YangMills.WilsonProof.NativeSupport.WardStressSeries

/-! The normalization and Ward identities depend on the continuum correlation array. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.CorrelationMatching

open Matching

/-- Embed the correlation array into the input type for the Ward and
normalization equations. Those equations use only its correlation component. -/
def coefficientTable (g : GaugeGroup) : MSbar.Coefficients (maxwellReference g) where
  correlation := graphCoefficient g
  ope := 0

/-- The position tests, formal conversion and numerical adjustment are calibrated
against the group’s continuum graph coefficients. -/
def GroupCalibration (g : GaugeGroup) (N : Normalization g) : Prop :=
  CalibrationLaws g (coefficientTable g) N

/-- The conservation and translation Ward equations for a stress series in the
converted continuum correlations. -/
def WardIdentities (g : GaugeGroup) (S : Conversion (maxwellReference g))
    (P : WardStress.Series (maxwellReference g)) : Prop :=
  WardStress.Determined (coefficientTable g) S P

end YangMills.CorrelationMatching
