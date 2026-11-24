import YM.Integration.WilsonSurveyedColorHomeDeck

/-! The dimensional source of each named field as a literal finite linear
combination of the fixed Plot optics, before any integrations or pole cuts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorNamedBasis
open Labels MS MS.Arts MS.Motif.Literal MS.Theater MS.Land MS.Local.Physical
open FVA2 FVA2.O.Score FVA2.Position.OpenAxis
open WilsonSurveyedColorCurvature WilsonSurveyedColorOpenIndex WilsonSurveyedColorNormalizers
open WilsonSurveyedColorHomeDeck WilsonSurveyedColorNominated
open scoped Classical BigOperators Matrix
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "B" => Press.portDeck G

def raw (G : Gauge) (h : ℕ) : Board G h →ₗ[ℝ] Box (Mob G) :=
  ∑ r : Fin (h+1), invoice G h r.val ∘ₗ Resume (Press.portDeck G) h r.val ∘ₗ LinearMap.proj r

theorem atRank {h : ℕ} (r : Fin (h+1)) (v : (Press.portDeck G).carries (h:ℤ) r.val) :
    raw G h (Pi.single r v) = invoice G h r.val (Resume B h r.val v) := by
  unfold raw
  rw [LinearMap.sum_apply,Finset.sum_eq_single r]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem original {h : ℕ} (i : Grade G h) :
    raw G h (WilsonSurveyedColorHomeDeck.basis G h i) = (Plot B).optics h i := by
  rw [WilsonSurveyedColorHomeDeck.basis,Pi.basis_apply,atRank]
  rfl

theorem oneAxis (N : Normalizes U) {h : ℕ} (r : Fin (h+1)) (v : (Press.portDeck G).carries (h:ℤ) r.val) :
    wheel U N h (Pi.single r v) = Pi.single r (axis U N h r.val v) := by
  funext j
  by_cases e : j = r
  · subst j
    simp [wheel]
  · simp [wheel,Pi.single_eq_of_ne e]

def casting (N : Normalizes U) (h : ℕ) : Matrix (Grade G h) (Grade G h) ℝ :=
  (LinearMap.toMatrix (WilsonSurveyedColorHomeDeck.basis G h) (WilsonSurveyedColorHomeDeck.basis G h) (wheel U N h))ᵀ

theorem entry (N : Normalizes U) (h : ℕ) (i j : Grade G h) :
    casting U N h i j = (WilsonSurveyedColorHomeDeck.basis G h).repr (wheel U N h (WilsonSurveyedColorHomeDeck.basis G h i)) j :=
  LinearMap.toMatrix_apply .. 

theorem reversed (N : Normalizes U) (N' : Normalizes U.symm) (h : ℕ) :
    casting U N h * casting U.symm N' h = 1 := by
  unfold casting
  rw [← Matrix.transpose_mul,← LinearMap.toMatrix_comp,undone,LinearMap.toMatrix_id,
    Matrix.transpose_one]

variable [PreconnectedSpace G.El] (hG : G.Simple) (same : Preserves U)

theorem actual (i : Rake.Label B) :
    additional hG U same i =
      ∑ j : Grade G i.h, casting U (groupAction hG U same) i.h i.item j • (Plot B).optics i.h j := by
  let N := groupAction hG U same
  have hi : raw G i.h (wheel U N i.h (WilsonSurveyedColorHomeDeck.basis G i.h i.item)) = additional hG U same i := by
    rw [WilsonSurveyedColorHomeDeck.basis,Pi.basis_apply,oneAxis,atRank,print]
    rfl
  rw [← hi]
  simp_rw [← original,← map_smul,entry]
  rw [← map_sum,(WilsonSurveyedColorHomeDeck.basis G i.h).sum_repr]

end YM.Integration.WilsonSurveyedColorNamedBasis
end
