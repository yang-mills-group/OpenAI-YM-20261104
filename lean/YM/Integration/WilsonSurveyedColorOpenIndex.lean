import YM.Integration.WilsonSurveyedColorPlot
import YM.FVA2.Extras.Result

/-! Promotion of an orthogonal color rotation as an additional field of the
same dimensionally regulated MS prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorOpenIndex
open Labels MS MS.Arts MS.Motif MS.Motif.Literal MS.Theater MS.Land MS.Local.Physical
open FVA2 FVA2.Position.OpenAxis FVA2.Extras
open WilsonSurveyedColorPlot WilsonSurveyedColorQuotient WilsonSurveyedColorCurvature
open scoped Classical
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
variable {h n : ℕ}

def Normalizes : Prop :=
  ∀ g : G.El, ∃ t : G.El, ∀ x : G.Color, U (G.adjoint g x) = G.adjoint t (U x)

theorem admitted (N : Normalizes U) (s : Film0 G h n) :
    changed (color U) s.val ∈ Film0 G h n := by
  obtain ⟨deg, gauge, real⟩ := (cinema s.val).mp s.property
  apply (cinema _).mpr
  refine ⟨still _ deg, ?_, ?_⟩
  · intro A g
    obtain ⟨t,ht⟩ := N g
    simp only [eval_changed]
    have comm : changedJet (color U) (colored g A) = colored t (changedJet (color U) A) := by
      funext j
      apply Subtype.ext
      funext k
      ext1 x
      exact ht _
    rw [comm]
    exact gauge _ _
  · apply eval_ext
    intro A
    rw [conj_value, eval_changed, ← conj_value, real]

def promoted (N : Normalizes U) (s : Film0 G h n) : Film0 G h n :=
  ⟨changed (color U) s.val, admitted U N s⟩

theorem sameSource (N : Normalizes U) (hu : Preserves U) (s : Film0 G h n)
    (z : ℂ) (m : ℕ) :
    turn U (Literal.value (Mob G) z (invoice G h n s) m) =
      Literal.value (Mob G) z (invoice G h n (promoted U N s)) m := by
  rw [invoiceAt U hu s, priceR]
  rfl

theorem singleBook {B : Booked (Press.portDeck G)}
    (M : MS_Data G B) (a : ℝ) (N : Normalizes U) (s : Film0 G h n) :
    ∃ p Y Q, Determined h (linear (Mob G) (invoice G h n (promoted U N s))) M a p Y Q := by
  exact gallery (M := M) (a := a) (invoice G h n (promoted U N s)) _ (invoiceC _)

end YM.Integration.WilsonSurveyedColorOpenIndex
end
