import YM.Integration.WilsonOriginalFiledJetStep
import YM.Integration.WilsonOriginalLowFourierJets

/-! The true iterated mixed derivative on the localized box has the product
of its original frequency coordinates, including vanishing factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedFourierRead
open Set UnitAddTorus
open scoped Interval BigOperators
theorem original {d : ℕ} (j : ℕ) (direction : ℕ → Fin (d+1))
    (fields : ℕ → C(UnitAddTorus (Fin (d+1)),ℂ))
    (partials : ∀ k < j, ∀ rest : Fin d → UnitAddCircle, ∀ x ∈ [[(0:ℝ),1]],
      HasDerivAt (fun t : ℝ => fields k ((direction k).insertNth (t:UnitAddCircle) rest))
        (fields (k+1) ((direction k).insertNth (x:UnitAddCircle) rest)) x) (v : Fin (d+1) → ℤ) :
    mFourierCoeff (fields j) v =
      WilsonOriginalLowFourierJets.jet (fun k : Fin j => direction k.val)
        (fun _ => 2*(Real.pi:ℂ)*Complex.I) v * mFourierCoeff (fields 0) v := by
  have earned (n : ℕ) (h : n ≤ j) : mFourierCoeff (fields n) v =
      (∏ k : Fin n, (2*(Real.pi:ℂ)*Complex.I)*(v (direction k.val):ℂ))*mFourierCoeff (fields 0) v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← WilsonOriginalFiledJetStep.original (fields n) (fields (n+1)) (direction n)
        (partials n (by omega)) v,ih (by omega),Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      ring
  exact earned j le_rfl
end YM.Integration.WilsonOriginalMixedFourierRead
