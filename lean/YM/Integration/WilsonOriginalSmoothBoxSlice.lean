import YM.Integration.WilsonOriginalHomogeneousRealGerm
import YM.Integration.WilsonOriginalCompactAxisExpense

/-! Real smoothness of a localized section on the actual periodic chart,
including the two endpoints of an axis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSmoothBoxSlice
open Filter Set AddCircle UnitAddTorus Finset
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalPhysicalBoxSlices (positions slice evaluate)
open WilsonOriginalCompactAxisExpense (pulled peers)
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalGevreyCutoffDisc (leaf)
open scoped Topology ContDiff

theorem original {d : ℕ} (i : Fin (d+1)) (a l h : Fin (d+1) → ℝ)
    (f : (Fin (d+1) → ℝ) → ℂ) (rest : Fin d → UnitAddCircle) (x : ℝ)
    (left : a i < l i) (right : h i < a i+1) (hx : x ∈ Icc (a i) (a i+1))
    (field : ContDiffAt ℝ ∞ (fun t : ℝ => f (positions i a rest x + t • (Pi.single i (1:ℝ)))) 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ => localize a l h f (i.insertNth (t:UnitAddCircle) rest)) x := by
  have windowSmooth : ContDiffAt ℝ ∞ (fun t : ℝ => window (l i) (h i) (x+t)) 0 :=
    ((WilsonOriginalFiledBoxWindow.smooth _ _).comp (contDiff_const.add contDiff_id)).contDiffAt
  have moved : ContDiffAt ℝ ∞ (fun t : ℝ => slice i a l h f rest (x+t)) 0 := by
    simp_rw [pulled]
    exact contDiffAt_const.mul (windowSmooth.mul field)
  have smooth : ContDiffAt ℝ ∞ (slice i a l h f rest) x := by
    have shifted : ContDiffAt ℝ ∞ (fun t : ℝ => slice i a l h f rest (x+t)) (x-x) := by
      simpa using moved
    have undo : ContDiffAt ℝ ∞ (fun t : ℝ => t-x) x := contDiffAt_id.sub contDiffAt_const
    simpa [Function.comp_def,sub_eq_add_neg,add_left_comm,add_comm,add_assoc] using shifted.comp (f := fun t : ℝ => t-x) x undo
  simp only [evaluate]
  refine smooth.congr_of_eventuallyEq (WilsonOriginalPeriodicWindowGerm.germ _ left right ?_ hx)
  intro t ht
  have zero : window (l i) (h i) (positions i a rest t i) = 0 := by
    simp only [positions,Fin.insertNth_apply_same]
    rcases not_and_or.mp ht with b|b
    · simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp b).le)]
    · simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp b).le)]
  rw [WilsonOriginalPhysicalBoxSlices.slice,Finset.prod_eq_zero (mem_univ i) zero,zero_mul]

end YM.Integration.WilsonOriginalSmoothBoxSlice
