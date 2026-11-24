import YM.Integration.WilsonSurveyedColorNormalizers

/-! Simultaneous enrollment of all rotated sources of the nominated MS book.
Each marked completion and its physical coordinates are fixed before the
test, the spectator fields and the perturbative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorNominated
open MS MS.Plane MS.Arts MS.Motif MS.Theater MS.Motif.Literal MS.Dock MS.Land MS.Local.Physical
open FVA2 FVA2.Position.OpenAxis FVA2.Extras
open WilsonSurveyedColorOpenIndex WilsonSurveyedColorNormalizers
open WilsonSurveyedColorCurvature WilsonSurveyedColorQuotient
open scoped Classical
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
local notation "B" => (Press.portDeck G)

def prototype (i : Rake.Label B) : Film0 G i.h i.item.1.val :=
  Theater.Resume B i.h i.item.1.val (Module.finBasis ℝ _ i.item.2)

def additional (i : Rake.Label B) :=
  invoice G i.h i.item.1.val (promoted U (groupAction hG U same) (prototype i))

structure Source (M : MS_Data G (Plot B)) (a : ℝ) (i : Rake.Label B) where
  coefficients : ℕ → Package B i.h
  inserted : Blue G
  counterterms : CostsM G
  reduced : Determined i.h (Literal.linear (Mob G) (additional hG U same i))
    M a coefficients inserted counterterms

theorem existsSource (M : MS_Data G (Plot B)) (a : ℝ) (i : Rake.Label B) :
    Nonempty (Source hG U same M a i) := by
  obtain ⟨p,Y,Q,ok⟩ := singleBook U M a (groupAction hG U same) (prototype i)
  exact ⟨⟨p,Y,Q,ok⟩⟩

def field (M : MS_Data G (Plot B)) (a : ℝ) (i : Rake.Label B) :
    Source hG U same M a i := Classical.choice (existsSource hG U same M a i)

theorem actual (i : Rake.Label B) (z : ℂ) (k : ℕ) :
    turn U (Literal.value (Mob G) z ((Plot B).optics i.h i.item) k) =
      Literal.value (Mob G) z (additional hG U same i) k :=
  sameSource U (groupAction hG U same) same (prototype i) z k

end YM.Integration.WilsonSurveyedColorNominated
end
