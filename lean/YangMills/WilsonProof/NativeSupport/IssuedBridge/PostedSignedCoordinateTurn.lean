import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedPinFrame

noncomputable section
namespace IssuedBridge.PostedSignedCoordinateTurn
open YM YM.Maxwell YM.Maxwell.Free
open scoped Classical BigOperators

def axes (σ : Equiv.Perm Axis) (sign : Axis → ℝ) : Signed :=
  ⟨σ, fun a => decide (sign a = -1)⟩

theorem entries (σ : Equiv.Perm Axis) (sign : Axis → ℝ)
    (hs : ∀ a, sign a = 1 ∨ sign a = -1) (i a : Axis) :
    (axes σ sign).ortho.val i a = if i = σ a then sign a else 0 := by
  change (if σ a = i then (if decide (sign a = -1) then (-1:ℝ) else 1) else 0) = _
  rcases hs a with ha|ha <;> norm_num [ha, eq_comm]

theorem motion (σ : Equiv.Perm Axis) (sign : Axis → ℝ)
    (U : E4 ≃ₗᵢ[ℝ] E4) (hs : ∀ a, sign a = 1 ∨ sign a = -1)
    (hU : ∀ a, U (basis a) = sign a • basis (σ a)) (x : E4) :
    Ortho.move (axes σ sign).ortho x = U x := by
  let B := (EuclideanSpace.basisFun Axis ℝ).toBasis
  have cols (a : Axis) : Ortho.move (axes σ sign).ortho (basis a) = U (basis a) := by
    rw [hU]
    ext i
    change M4.move (axes σ sign).ortho.val (basis a) i = _
    simp only [M4.move_basis, entries σ sign hs, PiLp.smul_apply, basis_eq, smul_eq_mul]
    split <;> simp
  have eq : (Ortho.motion (axes σ sign).ortho).toLinearEquiv.toLinearMap =
      U.toLinearEquiv.toLinearMap := by
    apply B.ext
    intro a
    simpa only [B, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, Ortho.motion_at, basis] using cols a
  exact LinearMap.congr_fun eq x

theorem original {G : Gauge} (σ : Equiv.Perm Axis) (sign : Axis → ℝ)
    (U : E4 ≃ₗᵢ[ℝ] E4) (hs : ∀ a, sign a = 1 ∨ sign a = -1)
    (hU : ∀ a, U (basis a) = sign a • basis (σ a))
    (A : TaylorTower G) (j : ℕ) (a b : Axis) (v : Fin j → E4) :
    (solutionTurn (axes σ sign).ortho⁻¹ (A j)).val a b v =
      (sign a * sign b) • (A j).val (σ a) (σ b) (fun i => U (v i)) := by
  change turnJ (axes σ sign).ortho⁻¹ (A j).val a b v = _
  rw [turns_apply, inv_inv]
  simp only [inv_entry, entries σ sign hs, ite_mul, zero_mul, mul_ite, mul_zero,
    ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Function.comp_def, motion σ sign U hs hU]

end IssuedBridge.PostedSignedCoordinateTurn
end
