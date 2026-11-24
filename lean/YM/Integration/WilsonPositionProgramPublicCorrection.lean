import YM.Integration.WilsonPositionProgramPublicGram

/-! Solve the signed finite test matrix, retaining any shared measured column
exactly. All constants refer to the one submitted frame. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicCorrection
open Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

structure Receipt (A : E →ₗ[ℂ] E) (L : ℝ) where
  change : E ≃ₗ[ℂ] E
  reads : change.toLinearMap = A
  price : ∀ x, ‖change.symm x‖ ≤ L * ‖x‖

theorem integral (A : E →ₗ[ℂ] E) (near : ∀ x, ‖A x - x‖ ≤ (1/2:ℝ)*‖x‖) :
    Nonempty (Receipt A 2) := by
  have bound (x : E) : ‖x‖ ≤ 2*‖A x‖ := by
    have t : ‖x‖ ≤ ‖x-A x‖ + ‖A x‖ := by simpa only [sub_add_cancel] using norm_add_le (x-A x) (A x)
    rw [norm_sub_rev] at t
    linarith [near x]
  have inj : Injective A := by
    intro x y e
    have b:=bound (x-y)
    rw [map_sub,e,sub_self,norm_zero,mul_zero] at b
    exact sub_eq_zero.mp (norm_le_zero_iff.mp b)
  let U := LinearEquiv.ofBijective A ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩
  refine ⟨⟨U,rfl,fun x => ?_⟩⟩
  have b:=bound (U.symm x)
  change ‖U.symm x‖ ≤ 2*‖U (U.symm x)‖ at b
  simpa only [LinearEquiv.apply_symm_apply] using b

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

omit [FiniteDimensional ℂ E] in
/-- The correction takes the other signed column to its own measured target. -/
theorem compare (L : P →ₗ[ℂ] E) (weak sharp : E →ₗ[ℂ] P) {k : ℝ}
    (H : Receipt (L.comp sharp) k) (hk : 0 ≤ k) (x : E) :
    let u := H.change.symm (L (weak x))
    L (sharp u) = L (weak x) ∧
    ‖u - x‖ ≤ k * ‖L.toContinuousLinearMap‖ * ‖weak x - sharp x‖ ∧
    (weak x = sharp x → u = x) := by
  let u := H.change.symm (L (weak x))
  have apply (v : E) : H.change v = L (sharp v) := LinearMap.congr_fun H.reads v
  have equal : L (sharp u) = L (weak x) := by rw [←apply];exact H.change.apply_symm_apply _
  have pre : H.change.symm (L (weak x-sharp x)) = u-x := by
    rw [map_sub,map_sub,←apply,LinearEquiv.symm_apply_apply]
  refine ⟨equal,?_,fun eq => ?_⟩
  · calc
      _ = ‖H.change.symm (L (weak x-sharp x))‖ := congrArg norm pre.symm
      _ ≤ k * ‖L (weak x-sharp x)‖ := H.price _
      _ ≤ k * (‖L.toContinuousLinearMap‖ * ‖weak x-sharp x‖) :=
        mul_le_mul_of_nonneg_left (L.toContinuousLinearMap.le_opNorm _) hk
      _ = _ := (mul_assoc ..).symm
  · apply H.change.injective
    rw [apply,apply,equal,eq]

end YM.Integration.WilsonPositionProgramPublicCorrection
