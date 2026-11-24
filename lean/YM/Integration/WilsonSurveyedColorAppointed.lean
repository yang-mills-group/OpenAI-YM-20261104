import YM.Integration.WilsonSurveyedColorNominatedSection

/-! The computed real change and its inverse on the actual named MS fields.
Both are constant in the coupling, on every nominated reporting scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorAppointed
open PowerSeries Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open FVA2.O FVA2.O.Score FVA2.O.Project FVA2.O.Read FVA2.Position.OpenAxis
open MS MS.Land MS.Fleet MS.Theater MS.Book.Program
open WilsonSurveyedColorOpenIndex WilsonSurveyedColorCurvature WilsonSurveyedColorNormalizers
open WilsonSurveyedColorNamedBasis WilsonSurveyedColorNominatedSection
open scoped Classical BigOperators Matrix
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)

def scalar : ℝ →+* Cn := PowerSeries.C.comp (algebraMap ℝ ℂ)

def chart (N : Normalizes U) : Cast G := fun d => scalar.mapMatrix (casting U N d)

theorem undo (N : Normalizes U) (N' : Normalizes U.symm) :
    chart U N * chart U.symm N' = 1 := by
  funext d
  change scalar.mapMatrix (casting U N d) * scalar.mapMatrix (casting U.symm N' d) = 1
  rw [← map_mul,reversed,map_one]

variable [PreconnectedSpace G.El] (hG : G.Simple) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ)
local notation "N" => groupAction hG U same
local notation "N'" => groupAction hG U.symm (reversedCartan U same)

theorem input : WilsonSurveyedColorScore.change hG U same M a = chart U N := by
  funext d
  ext i j q
  change PowerSeries.coeff q (PowerSeries.mk _) =
    PowerSeries.coeff q (PowerSeries.C (casting U N d i j : ℂ))
  rw [PowerSeries.coeff_mk,coefficients,PowerSeries.coeff_C]
  by_cases he : q = 0 <;> simp [he]

theorem output :
    WilsonSurveyedColorNominatedOPE.inverse hG U same M a = chart U.symm N' := by
  let V := WilsonSurveyedColorNominatedOPE.inverse hG U same M a
  have hl : V * chart U N = 1 := by
    rw [←input U hG same M a]
    exact WilsonSurveyedColorNominatedOPE.leftInverse hG U same M a (nondegenerate hG U same M a)
  change V = _
  calc V = V * 1 := (mul_one _).symm
       _ = V * (chart U N * chart U.symm N') := by rw [undo]
       _ = chart U.symm N' := by rw [←mul_assoc,hl,one_mul]

theorem correlations :
    WilsonSurveyedColorMeasuredAlbum.measured hG U same M a =
      marking (chart U N) (install (Equator.wave a M)) := by
  rw [WilsonSurveyedColorMeasuredAlbum.rows,input]

theorem ordinary (Z : WilsonPrescription G) (dial : Bool) {n : ℕ} (u : Scan G n) (r : ℝ) :
    let T := chart U N
    let V := chart U.symm N'
    let c := holding PowerSeries.X T V (Canon.LogPricing (Equator.wave a M))
    OPEA (WilsonSurveyedColorMeasuredAlbum.measured hG U same M a) u (c u) ∧
      Canon.Gift_shape T PowerSeries.X u
        (fun v => Canon.OPECoefficients (Equator.wave a M) v r) (QuoteP u (c u) r) := by
  have h := WilsonSurveyedColorNominatedSection.ordinary hG U same M a Z dial u r
  dsimp only at h ⊢
  rwa [input U hG same M a,output U hG same M a] at h

end YM.Integration.WilsonSurveyedColorAppointed
end
