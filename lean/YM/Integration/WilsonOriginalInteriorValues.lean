import YM.Integration.WilsonOriginalFiledBoxWindow
import YM.Integration.WilsonOriginalMeasuredBoxResidual

/-! Removing the genuine compact cutoff on its closed interior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalInteriorValues
open Set AddCircle Finset
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalGevreyWindow (window)
open scoped Topology BigOperators

def weight {d : ℕ} (l h x : Fin d → ℝ) : ℂ := ∏ i,window (l i) (h i) (x i)

theorem realValue {d : ℕ} (l h x : Fin d → ℝ) (inBox : ∀ i, x i ∈ Ioc (0:ℝ) 1)
    (f : (Fin d → ℝ) → ℂ) :
    localize 0 l h f (fun i => (x i : UnitAddCircle)) = weight l h x*f x := by
  have seat (i : Fin d) : (equivIoc (1:ℝ) 0 (x i)).val = x i :=
    equivIoc_coe_of_mem (by simpa using inBox i)
  simp only [localize,Pi.zero_apply,seat,weight]

theorem floor {d : ℕ} (l h x : Fin d → ℝ) {δ : ℝ} (pos : 0 < δ)
    (lo : ∀ i, δ ≤ x i-l i) (hi : ∀ i, δ ≤ h i-x i) :
    0 < ((expNegInvGlue δ)^2)^d ∧ ((expNegInvGlue δ)^2)^d ≤ ‖weight l h x‖ := by
  have slot := fun i => WilsonOriginalFiledBoxWindow.interior pos (lo i) (hi i)
  constructor
  · exact pow_pos (pow_pos (expNegInvGlue.pos_of_pos pos) 2) _
  · rw [weight,norm_prod]
    simpa using (prod_le_prod (s:=univ) (f:=fun _ : Fin d => (expNegInvGlue δ)^2)
      (g:=fun i => ‖window (l i) (h i) (x i)‖) (fun i _ => sq_nonneg _) (fun i _ => (slot i).2))

theorem original {d : ℕ} (l h x : Fin d → ℝ) (inBox : ∀ i, x i ∈ Ioc (0:ℝ) 1)
    (f : (Fin d → ℝ) → ℂ) (a : ℕ → (Fin d → ℝ) → ℂ) (u : ℝ) (p : ℕ)
    {δ : ℝ} (pos : 0 < δ) (lo : ∀ i, δ ≤ x i-l i) (hi : ∀ i, δ ≤ h i-x i)
    {C : ℝ}
    (income : let z := fun i => (x i:UnitAddCircle)
      ‖localize 0 l h f z - ∑ k : Fin (p+1), (u:ℂ)^k.val*localize 0 l h (a k.val) z‖ ≤
        ((expNegInvGlue δ)^2)^d*C) :
    ‖f x-∑ k : Fin (p+1), (u:ℂ)^k.val*a k.val x‖ ≤ C := by
  obtain ⟨positive,lower⟩ := floor l h x pos lo hi
  dsimp only at income
  simp only [realValue l h x inBox] at income
  apply le_of_mul_le_mul_left _ positive
  apply (mul_le_mul_of_nonneg_right lower (norm_nonneg _)).trans
  rw [← norm_mul,mul_sub,mul_sum]
  have swap (k : Fin (p+1)) : weight l h x * ((u:ℂ)^k.val*a k.val x) =
      (u:ℂ)^k.val*(weight l h x*a k.val x) := mul_left_comm ..
  simp only [swap]
  exact income

end YM.Integration.WilsonOriginalInteriorValues
