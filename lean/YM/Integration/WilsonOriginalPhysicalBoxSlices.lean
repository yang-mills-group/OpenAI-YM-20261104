import YM.Integration.WilsonOriginalPeriodicWindowGerm

/-! The actual periodic derivative in one coordinate of the measured box is
its original real derivative, also at the two boundary representatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalBoxSlices
open Set Filter AddCircle UnitAddTorus Finset
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalGevreyCutoffDisc (leaf)
open scoped Topology

def positions {d : ℕ} (i : Fin (d+1)) (a : Fin (d+1) → ℝ)
    (rest : Fin d → UnitAddCircle) (t : ℝ) : Fin (d+1) → ℝ :=
  i.insertNth t (fun j => (AddCircle.equivIoc (1:ℝ) (a (i.succAbove j)) (rest j)).val)

def slice {d : ℕ} (i : Fin (d+1)) (a l h : Fin (d+1) → ℝ)
    (f : (Fin (d+1) → ℝ) → ℂ) (rest : Fin d → UnitAddCircle) (t : ℝ) : ℂ :=
  (∏ j, window (l j) (h j) (positions i a rest t j))*f (positions i a rest t)

theorem evaluate {d : ℕ} (i : Fin (d+1)) (a l h : Fin (d+1) → ℝ)
    (f : (Fin (d+1) → ℝ) → ℂ) (rest : Fin d → UnitAddCircle) (z : UnitAddCircle) :
    localize a l h f (i.insertNth z rest) = AddCircle.liftIoc (1:ℝ) (a i) (slice i a l h f rest) z := by
  have sites : (fun j => (AddCircle.equivIoc (1:ℝ) (a j) ((i.insertNth z rest : Fin (d+1) → UnitAddCircle) j)).val) =
      positions i a rest (AddCircle.equivIoc (1:ℝ) (a i) z).val := by
    funext j
    refine i.succAboveCases ?_ (fun k => ?_) j <;> simp [positions]
  change _ = slice i a l h f rest (AddCircle.equivIoc (1:ℝ) (a i) z).val
  simp only [localize,slice,sites]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [show (equivIoc (1:ℝ) (a j) ((i.insertNth z rest : Fin (d+1) → UnitAddCircle) j)).val = _ from congrFun sites j]

theorem original {d : ℕ} (i : Fin (d+1)) (a l h : Fin (d+1) → ℝ)
    (f : (Fin (d+1) → ℝ) → ℂ) (rest : Fin d → UnitAddCircle) (x : ℝ)
    (left : a i < l i) (right : h i < a i+1) (hx : x ∈ Icc (a i) (a i+1)) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => localize a l h f (i.insertNth (t:UnitAddCircle) rest)) x =
    iteratedDeriv k (slice i a l h f rest) x := by
  simp only [evaluate]
  apply WilsonOriginalPeriodicWindowGerm.original _ left right _ hx
  intro t ht
  have zero : window (l i) (h i) (positions i a rest t i) = 0 := by
    simp only [positions,Fin.insertNth_apply_same]
    rcases not_and_or.mp ht with b|b
    · simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp b).le)]
    · simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp b).le)]
  rw [slice,Finset.prod_eq_zero (mem_univ i) zero,zero_mul]

end YM.Integration.WilsonOriginalPhysicalBoxSlices
