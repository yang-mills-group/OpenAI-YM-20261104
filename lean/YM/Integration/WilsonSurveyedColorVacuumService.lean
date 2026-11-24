import YM.Integration.WilsonSurveyedColorVacuumTour
/-! The same nominated MS bulk and the actual transformed marks fund both
tours. The integrated connected returns agree before taking the ordinary
finite partition polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumService
open Function Set Filter Finset MeasureTheory MS
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City
open Wire Wind Signal Latch Job Belt Garment Outlook Rake Rake.Geo Land Local.Physical
open Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program Tide Vane
open FVA2 FVA2.Extras FVA2.O FVA2.O.Lives FVA2.O.Fuse FVA2.Position.OpenAxis
open WilsonSurveyedColorCurvature WilsonSurveyedColorSubtraction WilsonSurveyedColorNominated
open WilsonSurveyedColorHearing WilsonSurveyedColorVacuumBook WilsonSurveyedColorMinimal
open WilsonSurveyedColorVacuumTour
open scoped Classical BigOperators Topology
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ)
variable {W : Type} [LinearOrder W] (x : Rake.Position W Unit)
variable (u : W → Rake.Label (Press.portDeck G))
local notation "P" => frameF Unit a

local notation "V" => enrolled M a u
local notation "Q" => promoted hG U same M a u

theorem picture (hx : Mesh P x) (s : Finset W) (k : ℕ) :
    filed U (score a M x V s k) = score a M x Q s k := by
  have ht : Teams P M V x (score a M x V) := scoreK (originalSurvey M a x u) hx
  have hs : Teams P M Q x (score a M x Q) := scoreK (promotedSurvey hG U same M a x u) hx
  have hl : Tour (constantP G Unit (PlanetD G)) (constantP G Unit (PlanetD G)) P x false
      (approach P M) V (fun i => (u i).h) := builder M hx u
  exact WilsonSurveyedColorBank.together U hl (paid hG U same M a x u hx)
    ht hs (background U same M a) (foreground hG U same M a u) s k

theorem reported (hx : Mesh P x) (s : Finset W) (k : ℕ) :
    service a M Q x s k = Dial.tour M u a (fun i => x i ()) s k := by
  have hv := originalSurvey M a x u
  have hq := promotedSurvey hG U same M a x u
  have ht : Teams P M V x (score a M x V) := scoreK hv hx
  have hs : Teams P M Q x (score a M x Q) := scoreK hq hx
  have values (t : ℝ) : (fun (v : Finset W) (n : ℕ) => score a M x Q v n () t []) =
      (fun (v : Finset W) (n : ℕ) => score a M x V v n () t []) := by
    funext v n
    exact (congrFun (congrFun (congrFun (picture hG U same M a x u hx v n) ()) t) []).symm
  have left := Extras.evaluate_full ht hv hx () s k
  have right := Extras.evaluate_full hs hq hx () s k
  simp only [values] at right
  exact (tendsto_nhds_unique right left).trans (tourC hv hx u rfl s k)

end YM.Integration.WilsonSurveyedColorVacuumService
end
