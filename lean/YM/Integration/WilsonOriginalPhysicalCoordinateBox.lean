import YM.Integration.WilsonOriginalCompactPoseCover
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalCoordinateBox
open scoped Classical
def axes (n : ℕ) : (Fin (n*4) → ℝ) ≃ₗ[ℝ] Points n where
      toFun := fun v => points fun i => WithLp.toLp 2 fun a => v (finProdFinEquiv (i,a))
      invFun := fun x k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := by
        intro v
        funext k
        exact congrArg v (finProdFinEquiv.apply_symm_apply k)
      right_inv := by
        intro x
        ext i a
        change x (finProdFinEquiv.symm (finProdFinEquiv (i,a))).1
          (finProdFinEquiv.symm (finProdFinEquiv (i,a))).2 = _
        rw [Equiv.symm_apply_apply]

def coordinates (n : ℕ) : (Fin (n*4) → ℝ) ≃L[ℝ] Points n where
  toLinearEquiv := axes n
  continuous_toFun := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a => continuous_apply (finProdFinEquiv (i,a))))
  continuous_invFun := continuous_pi fun k =>
    (PiLp.continuous_apply 2 _ (finProdFinEquiv.symm k).2).comp
      (PiLp.continuous_apply 2 _ (finProdFinEquiv.symm k).1)
theorem original (n : ℕ) :
    ∃ m : ℕ, Nonempty ((Fin (m+1) → ℝ) ≃L[ℝ] Points (n+1)) := by
  refine ⟨n*4+3,?_⟩
  have count : n*4+3+1 = (n+1)*4 := by omega
  rw [count]
  exact ⟨coordinates _⟩
end YM.Integration.WilsonOriginalPhysicalCoordinateBox
