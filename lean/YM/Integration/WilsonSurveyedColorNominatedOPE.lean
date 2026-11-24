import YM.Integration.WilsonSurveyedColorMeasuredAlbum

/-! Ordinary OPE of the promoted named sections on the one MS vacuum, with
the physical series on every input and its inverse on the output. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorNominatedOPE
open PowerSeries Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open FVA2.O FVA2.O.Score FVA2.O.Project FVA2.O.Enh FVA2.O.Bind FVA2.O.Read
open MS MS.Land MS.Fleet MS.Theater MS.Book.Program FVA2.Position.OpenAxis
open WilsonSurveyedColorCurvature WilsonSurveyedColorNominated WilsonSurveyedColorScore
open scoped Classical BigOperators Matrix
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ)

def head (d : ℕ) : Matrix (Grade G d) (Grade G d) ℂ :=
  fun i j => ((field hG U same M a ⟨d,i⟩).coefficients 0 j : ℂ)

def inverse : Cast G := fun d => (change hG U same M a d)⁻¹

theorem leftInverse (born : ∀ d, (head hG U same M a d).det ≠ 0) :
    inverse hG U same M a * change hG U same M a = 1 := by
  funext d
  apply Matrix.nonsing_inv_mul
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [RingHom.map_det]
  exact isUnit_iff_ne_zero.mpr (born d)

theorem ordinary (Z : WilsonPrescription G) (dial : Bool) {n : ℕ} (u : Scan G n) (r : ℝ)
    (born : ∀ d, (head hG U same M a d).det ≠ 0) :
    let T := change hG U same M a
    let V := inverse hG U same M a
    let c := holding PowerSeries.X T V (Canon.LogPricing (Equator.wave a M))
    OPEA (WilsonSurveyedColorMeasuredAlbum.measured hG U same M a) u (c u) ∧
      Canon.Gift_shape T PowerSeries.X u
        (fun v => Canon.OPECoefficients (Equator.wave a M) v r) (QuoteP u (c u) r) := by
  obtain ⟨_,H⟩ := Main.wilson_to_MS Z hG M dial
  have hn : Rooted (PowerSeries.X : Cn) := by simp [Rooted]
  have inv := leftInverse hG U same M a born
  have ht : tune PowerSeries.X (install (Equator.wave a M)) = install (Equator.wave a M) := by
    funext n x p
    exact PowerSeries.X_subst _
  constructor
  · rw [WilsonSurveyedColorMeasuredAlbum.rows]
    simpa only [ExchangeA,ht] using
      paid_w (u := u) hn inv (H.separatedOPE a).continuum.works
  · intro x
    apply Gift.total hn
    exact rate inv

end YM.Integration.WilsonSurveyedColorNominatedOPE
end
