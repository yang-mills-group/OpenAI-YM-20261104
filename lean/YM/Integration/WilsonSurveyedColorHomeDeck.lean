import YM.Integration.WilsonSurveyedColorHomeLift

/-! Invertible action on the actual nonnegative-weight physical section. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorHomeDeck
open Labels MS MS.Theater MS.Land MS.Local.Physical FVA2 FVA2.O.Score
open WilsonSurveyedColorPlot WilsonSurveyedColorOpenIndex WilsonSurveyedColorHomeLift
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "B" => Press.portDeck G

def onFilm (N : Normalizes U) (h r : ℕ) : Module.End ℝ (Film0 G h r) where
  toFun := promoted U N
  map_add' _ _ := Subtype.ext (map_add (changed (color U)) _ _)
  map_smul' c p := Subtype.ext (map_smul ((changed (color U)).toLinearMap.restrictScalars ℝ) c p.val)

def axis (N : Normalizes U) (h r : ℕ) : Module.End ℝ ((Press.portDeck G).carries (h:ℤ) r) :=
  ((Allowed G h r).subtype ∘ₗ over0 G h r ∘ₗ onFilm U N h r ∘ₗ Resume B h r).codRestrict _ (by
    intro p
    let Y := promoted U N (Resume B h r p)
    have hx : orbit G Y.val ∈ Press.born G h r := by
      refine ⟨Y,?_⟩
      change orbit G (Press.refineF G h r (promoted U N (Resume B h r p))).val = _
      rw [preserves,Press.stageF]
    exact (congrArg (fun S : Submodule ℝ _ => orbit G Y.val ∈ S) (Press.level G h r)).mpr hx)

theorem print (N : Normalizes U) (h r : ℕ) (p : (Press.portDeck G).carries (h:ℤ) r) :
    Resume B h r (axis U N h r p) = promoted U N (Resume B h r p) := by
  apply (f_standard G h r).1
  apply Subtype.ext
  exact honor B (axis U N h r p)

theorem unpaint (N : Normalizes U) (N' : Normalizes U.symm) {h r : ℕ} (p : Film0 G h r) :
    promoted U.symm N' (promoted U N p) = p := by
  apply Subtype.ext
  apply eval_ext
  intro A
  change read A (changed (color U.symm) (changed (color U) p.val)) = _
  rw [eval_changed,eval_changed]
  have e : changedJet (color U) (changedJet (color U.symm) A) = A := by
    funext j
    apply Subtype.ext
    funext k
    ext1 v
    exact U.apply_symm_apply _
  rw [e]

theorem undo (N : Normalizes U) (N' : Normalizes U.symm) {h r : ℕ}
    (p : (Press.portDeck G).carries (h:ℤ) r) : axis U.symm N' h r (axis U N h r p) = p := by
  have e : Resume B h r (axis U.symm N' h r (axis U N h r p)) = Resume B h r p := by
    rw [print,print,unpaint]
  apply Subtype.ext
  simpa only [honor] using congrArg (fun s : Film0 G h r => orbit G s.val) e

abbrev Board (G : Gauge) (h : ℕ) := (r : Fin (h+1)) → (Press.portDeck G).carries (h:ℤ) r.val
def basis (G : Gauge) (h : ℕ) : Module.Basis (Grade G h) ℝ (Board G h) :=
  Pi.basis fun r => Module.finBasis ℝ ((Press.portDeck G).carries (h:ℤ) r.val)

def wheel (N : Normalizes U) (h : ℕ) : Module.End ℝ (Board G h) :=
  LinearMap.pi (fun r => (axis U N h r.val).comp (LinearMap.proj r))

theorem undone (N : Normalizes U) (N' : Normalizes U.symm) (h : ℕ) :
    (wheel U.symm N' h).comp (wheel U N h) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext r
  exact undo U N N' (x r)

end YM.Integration.WilsonSurveyedColorHomeDeck
end
