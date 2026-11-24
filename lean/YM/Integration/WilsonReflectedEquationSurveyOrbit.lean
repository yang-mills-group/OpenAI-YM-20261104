import YM.Integration.WilsonMaxwellThermometerWardOrbitStation
import YM.Integration.WilsonMaxwellThermometerWardCredit
import YM.Integration.WilsonMaxwellThermometerWardLinear
import YM.Integration.WilsonOriginalPublicFigureWick
import YM.Integration.WilsonOriginalPivotWardSurvey

/-! The registered realization of the actual on-shell remainder, with the other
column taken from the appointed survey on the same finite inversion orbit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonReflectedEquationSurveyOrbit

open Function MeasureTheory Lattice Wilson RG Labels Source Push Maxwell XSpace
open PhysicalNext.Repeat.Legato PertExtension.Orb
open WilsonMaxwellThermometerWardConditional
open scoped Classical

variable {G : Gauge} (R : Run G) (W : Initialize G) {h d : ℕ}
    (V : SectionData (R.family.labels.level h)) (A : Mark.Weave G)

def registered (v : (R.family.labels.level h).Coeff) : (R.family.labels.level h).Coeff :=
  (R.family.labels.level h).coords (A h (WilsonOriginalPublicFigureWick.remainder W
    (R.family.labels.level h) v))

theorem original (granted : Mark.Portfolio R.family.params V (A h)) :
    ∃ r M : ℕ, ∀ (p : Period), M ≤ p.side.val → ∀ (x y : p.Sites),
      2*r+4 < separation x (-x) →
      (∀ e : Edge p.Sites, e.1 ∈ V.footprint x → e.1+step e.2 ∈ V.footprint x →
        far r x (reflect e)) →
      (∀ e : Edge p.Sites, e.1 ∈ (WilsonOriginalPivotWardSurvey.sectionAt R W d).footprint y →
        e.1+step e.2 ∈ (WilsonOriginalPivotWardSurvey.sectionAt R W d).footprint y →
          far r x e ∧ far r x (reflect e)) →
      ∀ (v : (R.family.labels.level h).Coeff) (b : (R.family.labels.level d).Coeff)
        (L K : ℂ →L[ℝ] ℝ) (t : ℝ), t ≠ 0 →
        preExpectation (fun U =>
          L (V.places (registered R W A v) x U) *
          K ((WilsonOriginalPivotWardSurvey.sectionAt R W d).places b y U)) t = 0 := by
  obtain ⟨r,M,pay⟩ := Mark.radiusH A V granted
  refine ⟨r,M,?_⟩
  intro p cut x y span clear room v b L K t live
  let S := WilsonOriginalPivotWardSurvey.sectionAt R W d
  let c := registered R W A v
  have null := WilsonOriginalPublicFigureWick.invisible W (R.family.labels.level h) v
  have paid := pay _ null
  have peer : Continuous (fun U : Config G p.side => K (S.places b y U)) :=
    K.continuous.comp (S.continuous_places b y)
  apply WilsonMaxwellThermometerWardCredit.normalize (V.continuous_places c x) peer L t
  apply WilsonMaxwellThermometerWardInversion.original (even_iff_two_dvd.mpr p.even)
    cut x span (V.continuous_evaluate c) paid
    (V.placed_local x c) clear
    (Complex.continuous_ofReal.comp peer) _ room t live
  intro U Z eq
  exact congrArg (fun z : ℂ => (K z : ℂ)) (S.placed_local y b U Z eq)

end YM.Integration.WilsonReflectedEquationSurveyOrbit
