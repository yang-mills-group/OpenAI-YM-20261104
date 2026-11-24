import YM.Integration.WilsonSurveyedColorOPE
import YM.Integration.WilsonSurveyedColorNamedTour

/-! The finite physical section change as a matrix of formal series on the
labelled basis used by the ordinary MS OPE. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorScore
open Function Finset PowerSeries MS MS.Land MS.Rake MS.Theater MS.Book.Program
open FVA2 FVA2.O FVA2.O.Score FVA2.Position.OpenAxis FVA2.Scale
open WilsonSurveyedColorNominated WilsonSurveyedColorCurvature
open scoped Classical BigOperators
variable {G : Gauge} {n : ℕ}

def change [PreconnectedSpace G.El] (hG : G.Simple) (U : G.Color ≃ₗᵢ[ℝ] G.Color)
    (same : Preserves U) (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ) : Cast G :=
  fun d i j => PowerSeries.mk fun k => ((field hG U same M a ⟨d,i⟩).coefficients k j : ℂ)

variable (T : Cast G) (p : Scan G n) (A : Scan G n → Cn)

def selected (S : Finset (Fin n)) (v : LivesP p) : Cn :=
  ∑ y : LivesP p, if ∀ i ∉ S, y i = v i then
    (∏ i ∈ S, T (p i).h (p i).item (y i)) * A (decode p y) else 0

theorem empty (v : LivesP p) : selected T p A ∅ v = A (decode p v) := by
  unfold selected
  rw [sum_eq_single v]
  · simp
  · intro y _ hy
    apply if_neg
    intro e
    exact hy (funext fun i => e i (by simp))
  · simp

theorem add (S : Finset (Fin n)) (v : LivesP p) (i : Fin n) (hi : i ∉ S) :
    selected T p A (insert i S) v =
      ∑ k : Grade G (p i).h, T (p i).h (p i).item k * selected T p A S (update v i k) := by
  unfold selected
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rw [sum_eq_single (y i)]
  · have eqv : (∀ j ∉ S, y j = update v i (y i) j) ↔
        ∀ j ∉ insert i S, y j = v j := by
      constructor
      · intro h j hj
        obtain ⟨ne,hs⟩ := not_or.mp (mt mem_insert.mpr hj)
        simpa only [update_of_ne ne] using h j hs
      · intro h j hj
        by_cases he : j = i
        · subst j; simp
        · rw [update_of_ne he]
          exact h j (by simpa only [mem_insert,not_or] using And.intro he hj)
    by_cases h : ∀ j ∉ insert i S, y j = v j
    · rw [if_pos h,if_pos (eqv.mpr h),prod_insert hi,mul_assoc]
    · rw [if_neg h,if_neg (mt eqv.mp h),mul_zero]
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro e
    exact hk (by simpa only [update_self] using (e i hi).symm)
  · simp

theorem complete (v : LivesP p) : selected T p A univ v = concert T p A := by
  simp [selected,concert,play,decode,report]

end YM.Integration.WilsonSurveyedColorScore
end
