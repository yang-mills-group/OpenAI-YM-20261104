import YM.Integration.WilsonSurveyedColorVacuumService
import YM.Integration.WilsonSurveyedColorAppointed

/-! Orthogonal Lie-algebra automorphisms simultaneously act on all named
insertions on the given continuum MS vacuum. Canonical uniqueness on that
very correlation law identifies the output and all ordinary OPE inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumPublic
open PowerSeries Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O
open FVA2.O.Score FVA2.O.Project FVA2.O.Read FVA2.Position.OpenAxis
open MS MS.Land MS.Fleet MS.Theater MS.Book.Program
open WilsonSurveyedColorOpenIndex WilsonSurveyedColorCurvature WilsonSurveyedColorNormalizers
open WilsonSurveyedColorNominatedSection WilsonSurveyedColorAppointed WilsonSurveyedColorMeasuredAlbum
open scoped Classical BigOperators Matrix
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ)
local notation "A" => install (Equator.wave a M)
local notation "C" => chart U (groupAction hG U same)
local notation "D" => chart U.symm (groupAction hG U.symm (reversedCartan U same))

theorem numerical : measured hG U same M a = A := by
  funext n x p
  by_cases hx : x ∈ conf n
  · ext k
    simp only [measured,if_pos hx,coeff_mk]
    rw [stock a M p hx]
    let z : MS.Rake.Position (Fin n) Unit := WilsonSurveyedColorMeasuredAlbum.points x
    have hz : MS.Rake.Mesh (MS.Tide.frameF Unit a) z :=
      WilsonSurveyedColorMeasuredAlbum.separated a x hx
    exact WilsonSurveyedColorVacuumService.reported (W := Fin n) hG U same M a z p hz Finset.univ k
  · simp [measured,install,hx]

theorem invariant : marking C A = A :=
  (WilsonSurveyedColorAppointed.correlations U hG same M a).symm.trans (numerical hG U same M a)

theorem ordinary (Z : WilsonPrescription G) (dial : Bool) {n : ℕ} (u : Scan G n) (r : ℝ) :
    holding PowerSeries.X C D (Canon.LogPricing (Equator.wave a M)) u =
      Canon.LogPricing (Equator.wave a M) u ∧
    Canon.Gift_shape C PowerSeries.X u
      (fun v => Canon.OPECoefficients (Equator.wave a M) v r)
      (Canon.OPECoefficients (Equator.wave a M) u r) := by
  have changed := WilsonSurveyedColorAppointed.ordinary U hG same M a Z dial u r
  dsimp only at changed
  rw [numerical hG U same M a] at changed
  obtain ⟨_,H⟩ := Main.wilson_to_MS Z hG M dial
  have eq := (H.separatedOPE a).continuum.unique u changed.1
  refine ⟨eq.symm,?_⟩
  have g := changed.2
  rw [←eq] at g
  exact g

end YM.Integration.WilsonSurveyedColorVacuumPublic
end
