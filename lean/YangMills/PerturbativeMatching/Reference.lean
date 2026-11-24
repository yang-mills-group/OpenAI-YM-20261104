import YangMills.PerturbativeMatching.GraphCoefficients
import YangMills.PerturbativeMatching.Calibration
import YangMills.PerturbativeMatching.WardIdentities
import MSOrdinaryOPE

set_option autoImplicit false
noncomputable section

namespace YangMills.PerturbativeMatching

/-- The continuum MS-bar correlations determine a unique ordinary OPE through
every finite output dimension, tested against arbitrary exterior insertions. -/
def OPEIsDetermined (g : GaugeGroup) : Prop :=
  MSbar.Ordinary.Determined (maxwellReference g) (graphCorrelation g)

/-- Both entries use the same continuum graph expansion. The OPE entry is the
unique field-valued coefficient characterized by its exterior correlations. -/
def msbarCoefficients (g : GaugeGroup) (determined : OPEIsDetermined g) :
    MSbar.Coefficients (maxwellReference g) where
  correlation := graphCorrelation g
  ope := MSbar.Ordinary.read (maxwellReference g) determined

/-- An OPE array satisfies the exterior characterization exactly when it is the
OPE entry of the reference. -/
theorem valid_iff_eq_reference (g : GaugeGroup) (determined : OPEIsDetermined g)
    (O : MSbar.Ordinary.OPE (maxwellReference g)) :
    MSbar.Ordinary.Valid (maxwellReference g) (graphCorrelation g) O ↔
      O = (msbarCoefficients g determined).ope := by
  constructor
  · exact MSbar.Ordinary.eq_read (maxwellReference g) determined
  · rintro rfl
    exact MSbar.Ordinary.read_valid (maxwellReference g) determined

/-- All perturbative data are fixed on the Maxwell fields of the gauge group. -/
structure Reference (g : GaugeGroup) where
  opeDetermined : OPEIsDetermined g
  scheme : PositionScheme g
  groupMenu_eq : some scheme.prescription = groupMenu g
  calibration : Calibration (msbarCoefficients g opeDetermined) scheme
  stressUnique : ∃! stress : Matching.WardStress.Series (maxwellReference g),
    Matching.WardStress.Determined (msbarCoefficients g opeDetermined) scheme.conversion stress

/-- The graph correlations and the ordinary OPE they determine. -/
abbrev Reference.coefficients {g : GaugeGroup} (reference : Reference g) :=
  msbarCoefficients g reference.opeDetermined

theorem Reference.scheme_unique {g : GaugeGroup} (left right : Reference g) :
    left.scheme = right.scheme :=
  left.calibration.uniqueAt right.calibration (Option.some.inj (left.groupMenu_eq.trans right.groupMenu_eq.symm))

/-- Any two calibrated references for the same gauge group agree. -/
instance {g : GaugeGroup} : Subsingleton (Reference g) where
  allEq left right := by
    have same := left.scheme_unique right
    cases left
    cases right
    cases same
    rfl

end YangMills.PerturbativeMatching
