import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Coefficients
import YangMills.WilsonProof.NativeSupport.MSOrdinaryOPE

set_option autoImplicit false
noncomputable section

namespace YangMills.OPEMatching

/-- The continuum MS-bar correlations determine a unique ordinary OPE through
every finite output dimension, tested against arbitrary exterior insertions. -/
def HasReference (g : GaugeGroup) : Prop :=
  MSbar.Ordinary.Determined (maxwellReference g) (CorrelationMatching.graphCoefficient g)

/-- Both entries use the same continuum graph expansion. The OPE entry is the
unique field-valued coefficient characterized by its exterior correlations. -/
def reference (g : GaugeGroup) (existsReference : HasReference g) :
    MSbar.Coefficients (maxwellReference g) where
  correlation := CorrelationMatching.graphCoefficient g
  ope := MSbar.Ordinary.read (maxwellReference g) existsReference

/-- An OPE array satisfies the exterior characterization exactly when it is the
OPE entry of the reference. -/
theorem valid_iff_eq_reference (g : GaugeGroup) (existsReference : HasReference g)
    (O : MSbar.Ordinary.OPE (maxwellReference g)) :
    MSbar.Ordinary.Valid (maxwellReference g) (CorrelationMatching.graphCoefficient g) O ↔
      O = (reference g existsReference).ope := by
  constructor
  · exact MSbar.Ordinary.eq_read (maxwellReference g) existsReference
  · rintro rfl
    exact MSbar.Ordinary.read_valid (maxwellReference g) existsReference

end YangMills.OPEMatching
