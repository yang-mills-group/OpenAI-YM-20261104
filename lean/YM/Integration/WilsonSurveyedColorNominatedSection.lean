import YM.Integration.WilsonSurveyedColorNamedBasis
import YM.Integration.WilsonSurveyedColorNamedArchive

/-! Full marked color convention for the actual nominated Plot, including
the input and output fields of its ordinary OPE. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorNominatedSection
open PowerSeries Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open FVA2.O FVA2.O.Score FVA2.O.Project FVA2.O.Read FVA2.Position.OpenAxis
open MS MS.Land MS.Fleet MS.Theater MS.Book.Program
open WilsonSurveyedColorCurvature WilsonSurveyedColorNormalizers WilsonSurveyedColorNominated
open WilsonSurveyedColorNamedBasis WilsonSurveyedColorNominatedOPE
open scoped Classical BigOperators Matrix
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ)
local notation "N" => groupAction hG U same

theorem coefficients (i : Rake.Label (Press.portDeck G)) :
    (field hG U same M a i).coefficients = Pi.single 0 (casting U N i.h i.item) :=
  WilsonSurveyedColorNamedArchive.coordinates M _ a _ (WilsonSurveyedColorNamedBasis.actual U hG same i)
    (field hG U same M a i).reduced

theorem first (d : ℕ) :
    head hG U same M a d = (casting U N d).map (algebraMap ℝ ℂ) := by
  ext i j
  change ((field hG U same M a ⟨d,i⟩).coefficients 0 j : ℂ) = _
  rw [coefficients,Pi.single_eq_same]
  rfl

include same in
omit [PreconnectedSpace G.El] in
theorem reversedCartan : Preserves U.symm := by
  intro x y z
  simpa using (same (U.symm x) (U.symm y) (U.symm z)).symm

theorem nondegenerate (d : ℕ) : (head hG U same M a d).det ≠ 0 := by
  have N' := groupAction hG U.symm (reversedCartan U same)
  have H := congrArg Matrix.det (reversed U N N' d)
  rw [Matrix.det_mul,Matrix.det_one] at H
  have hc : (casting U N d).det ≠ 0 := by
    intro e
    rw [e,zero_mul] at H
    exact zero_ne_one H
  rw [first]
  change ((algebraMap ℝ ℂ).mapMatrix (casting U N d)).det ≠ 0
  rw [←RingHom.map_det]
  exact (map_ne_zero (algebraMap ℝ ℂ)).mpr hc

theorem ordinary (Z : WilsonPrescription G) (dial : Bool) {n : ℕ} (u : Scan G n) (r : ℝ) :
    let T := WilsonSurveyedColorScore.change hG U same M a
    let V := inverse hG U same M a
    let c := holding PowerSeries.X T V (Canon.LogPricing (Equator.wave a M))
    OPEA (WilsonSurveyedColorMeasuredAlbum.measured hG U same M a) u (c u) ∧
      Canon.Gift_shape T PowerSeries.X u
        (fun v => Canon.OPECoefficients (Equator.wave a M) v r) (QuoteP u (c u) r) :=
  WilsonSurveyedColorNominatedOPE.ordinary hG U same M a Z dial u r (nondegenerate hG U same M a)

end YM.Integration.WilsonSurveyedColorNominatedSection
end
