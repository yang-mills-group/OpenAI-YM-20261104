import YM.Integration.WilsonSurveyedColorVacuumBook
import YM.Integration.WilsonSurveyedColorMinimal

/-! The same nominated MS bulk and the actual transformed marks fund both
tours. The integrated connected returns agree before taking the ordinary
finite partition polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumTour
open Function Set Filter Finset MeasureTheory MS
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City
open Wire Wind Signal Latch Job Belt Garment Outlook Rake Rake.Geo Land Local.Physical
open Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program Tide Vane
open FVA2 FVA2.Extras FVA2.O FVA2.O.Lives FVA2.O.Fuse FVA2.Position.OpenAxis
open WilsonSurveyedColorCurvature WilsonSurveyedColorSubtraction WilsonSurveyedColorNominated
open WilsonSurveyedColorHearing WilsonSurveyedColorVacuumBook WilsonSurveyedColorMinimal
open scoped Classical BigOperators Topology
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ)
variable {W : Type} (x : Rake.Position W Unit)
variable (u : W → Rake.Label (Press.portDeck G))
local notation "P" => frameF Unit a

omit [PreconnectedSpace G.El] in
theorem archived (h : ℕ) (F H : ℕ → Flats G)
    (left : ∀ k, Stay h (F k)) (right : ∀ k, Stay h (H k))
    (he : ∀ k, Pact (ledger U (F k)) (H k)) (k : ℕ) :
    filed U (circle (frameF Unit a).η (Archive h F) k) = circle (frameF Unit a).η (Archive h H) k := by
  funext i t
  exact congrFun (finiteGerm U (he k) (left k) (right k) t ((frameF Unit a).η i)) 0

omit [PreconnectedSpace G.El] in
theorem authentic {X : ℕ → Flats G} {q src : ℕ → Coat G} {h : ℕ}
    (H : comet h 0 M.bulk src X q) :
    (∀ k, Tip P false false h (letIn h (logMass a) X k)) ∧
      Ven (fun _ => planeF) (constantP G Unit (PlanetD G)) (constantP G Unit (PlanetD G))
        (approach P M) (letIn h (logMass a) X) := by
  constructor
  · intro n
    have hh := Host.host (gang (H n))
    exact ⟨collectD hh,nameD_warm hh,sund P _ hh⟩
  · intro n
    refine ⟨nameD_warm (Host.host (gang (H n))),?_⟩
    intro i w t
    have hg := pour (spaceD G) (Outlook.roadM M.bulkOK H) ((frameF Unit a).η i) w n t
    rw [ergo (η:=(frameF Unit a).η)] at hg
    exact hg

def enrolled := rowM P M ∘ u
def promoted := fun i => letIn (u i).h (logMass a) (field hG U same M a (u i)).inserted

omit [PreconnectedSpace G.El] in
theorem originalSurvey : Survey P M (enrolled M a u) x := fun i =>
  Estate (cometClean (M.markOK _ (u i).item)) (Response.visit _) _

theorem promotedSurvey : Survey P M (promoted hG U same M a u) x := fun i =>
  (field hG U same M a (u i)).reduced.usable (x i)

theorem paid (hx : Mesh P x) :
    Tour (constantP G Unit (PlanetD G)) (constantP G Unit (PlanetD G)) P x false
      (approach P M) (promoted hG U same M a u) (fun i => (u i).h) :=
  ⟨hx,masterD ..,fun n _ => tagD P M n,fun i n =>
    (authentic M a (field hG U same M a (u i)).reduced.okay).1 n,
    fun i => (authentic M a (field hG U same M a (u i)).reduced.okay).2⟩

omit [PreconnectedSpace G.El] in
include same in
theorem background (n : ℕ) : filed U (approach P M n) = approach P M n :=
  archived U a 4 _ _ (fun i => (gang (M.bulkOK i)).dost)
    (fun i => (gang (M.bulkOK i)).dost) (vacuum U same M) n

theorem foreground (i : W) (n : ℕ) :
    filed U (enrolled M a u i n) = promoted hG U same M a u i n :=
  archived U a (u i).h _ _ (fun k => (gang (M.markOK _ (u i).item k)).dost)
    (fun k => (gang ((field hG U same M a (u i)).reduced.okay k)).dost)
    (inserted hG U same M a (u i)) n

end YM.Integration.WilsonSurveyedColorVacuumTour
end
