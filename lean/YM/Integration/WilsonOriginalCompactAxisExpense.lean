import YM.Integration.WilsonOriginalPhysicalBoxSlices

/-! When the genuine physical direction is varied, all the other cutoff
coordinates remain on the same measured field and cost at most one. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactAxisExpense
open Set AddCircle UnitAddTorus Finset
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalPhysicalBoxSlices (positions)
open WilsonOriginalGevreyWindow (window)

theorem moved {d : ℕ} (i : Fin (d+1)) (a : Fin (d+1) → ℝ)
    (rest : Fin d → UnitAddCircle) (x t : ℝ) :
    positions i a rest (x+t) = positions i a rest x + t • (Pi.single i (1:ℝ)) := by
  funext j
  refine i.succAboveCases ?_ (fun k => ?_) j <;> simp [positions]

def peers {d : ℕ} (i : Fin (d+1)) (a l h : Fin (d+1) → ℝ)
    (rest : Fin d → UnitAddCircle) : ℂ :=
  ∏ j, window (l (i.succAbove j)) (h (i.succAbove j))
    (equivIoc (1:ℝ) (a (i.succAbove j)) (rest j)).val

theorem peers_bound {d : ℕ} (i : Fin (d+1)) (a l h : Fin (d+1) → ℝ)
    (rest : Fin d → UnitAddCircle) : ‖peers i a l h rest‖ ≤ 1 := by
  rw [peers,norm_prod]
  apply prod_le_one
  · exact fun _ _ => norm_nonneg _
  · intro j _
    simpa using WilsonOriginalGevreyWindow.original (l (i.succAbove j)) (h (i.succAbove j))
      (equivIoc (1:ℝ) (a (i.succAbove j)) (rest j)).val 0

theorem pulled {d : ℕ} (i : Fin (d+1)) (a l h : Fin (d+1) → ℝ)
    (rest : Fin d → UnitAddCircle) (f : (Fin (d+1) → ℝ) → ℂ) (x t : ℝ) :
    WilsonOriginalPhysicalBoxSlices.slice i a l h f rest (x+t) = peers i a l h rest * (window (l i) (h i) (x+t)*
      f (positions i a rest x + t • (Pi.single i (1:ℝ)))) := by
  rw [WilsonOriginalPhysicalBoxSlices.slice,Fin.prod_univ_succAbove _ i,← moved i a rest x t]
  simp only [peers,positions,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  ring

theorem original {d : ℕ} (i : Fin (d+1)) (a l h : Fin (d+1) → ℝ)
    (rest : Fin d → UnitAddCircle) (f : (Fin (d+1) → ℝ) → ℂ) {x : ℝ}
    (left : a i < l i) (right : h i < a i+1) (hx : x ∈ Icc (a i) (a i+1)) (k : ℕ) :
    ‖iteratedDeriv k (fun t : ℝ => localize a l h f (i.insertNth (t:UnitAddCircle) rest)) x‖ ≤
      ‖iteratedDeriv k (fun t : ℝ => window (l i) (h i) (x+t)*
        f (positions i a rest x+t • (Pi.single i (1:ℝ)))) 0‖ := by
  rw [WilsonOriginalPhysicalBoxSlices.original i a l h f rest x left right hx k]
  have shift := congrFun (iteratedDeriv_comp_const_add k (WilsonOriginalPhysicalBoxSlices.slice i a l h f rest) x) 0
  rw [add_zero] at shift
  rw [← shift]
  simp_rw [pulled]
  rw [iteratedDeriv_const_mul_field,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (peers_bound _ _ _ _ _)

end YM.Integration.WilsonOriginalCompactAxisExpense
