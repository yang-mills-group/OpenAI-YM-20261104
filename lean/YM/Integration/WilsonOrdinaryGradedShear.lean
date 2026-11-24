import YM.Integration.WilsonOrdinaryMarchAnchor

/-! Factor a true flagged change into the map on its engineering grades and an
explicit, affordable shear that acts as identity on each grade. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryGradedShear
open Filter Set Spec Climb OPE RG12 RG12.Frames
open scoped Topology BigOperators Classical
variable {d : ℕ} (V : Grade d → Type) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
set_option quotPrecheck false
local notation "X" => Col V

def diagonalMap (A : BlockMatrix V) : BlockMatrix V := LinearMap.pi fun i =>
  (LinearMap.proj i).comp (A.comp ((LinearMap.single ℂ V i).comp (LinearMap.proj i)))

@[simp] theorem atGrade (A : BlockMatrix V) (x : X) (i : Grade d) :
    diagonalMap V A x i = block V A i i (x i) := rfl

private lemma dtri (A : BlockMatrix V) : triangular V (diagonalMap V A) := by
  intro i j h x; change block V A i i (Pi.single j x i) = 0
  rw [Pi.single_eq_of_ne (ne_of_gt h),zero_block]

variable [∀ i, FiniteDimensional ℂ (V i)]

def diagonal (A : X ≃ₗ[ℂ] X) (flagged : triangular V A.toLinearMap) : X ≃ₗ[ℂ] X where
  toLinearMap := diagonalMap V A.toLinearMap
  invFun := diagonalMap V A.symm.toLinearMap
  left_inv x := funext fun i => inv_diag (V:=V) flagged.inv i (x i)
  right_inv x := funext fun i => inv_diag (V:=V) flagged i (x i)

def shear (A : X ≃ₗ[ℂ] X) (h : triangular V A.toLinearMap) : X ≃ₗ[ℂ] X :=
  (diagonal V A h).trans A.symm

theorem compensate (A : X ≃ₗ[ℂ] X) (h : triangular V A.toLinearMap) (x : X) :
    A (shear V A h x)=diagonal V A h x := A.apply_symm_apply _

theorem acts (A : X ≃ₗ[ℂ] X) (h : triangular V A.toLinearMap) :
    triangular V (shear V A h).toLinearMap ∧
      ∀ i : Grade d, ∀ x : V i, block V (shear V A h).toLinearMap i i x = x := by
  have hd := dtri V A.toLinearMap
  refine ⟨h.inv.comp hd,?_⟩
  intro i x
  have ground := (triangular_iff_stays V _).mp hd i (put V i x) (put_flag i i x le_rfl)
  calc
    _ = block V A.symm.toLinearMap i i (diagonalMap V A.toLinearMap (put V i x) i) := same_diag h.inv ground
    _ = block V A.symm.toLinearMap i i (block V A.toLinearMap i i x) := by rw [atGrade,put,Pi.single_eq_same]
    _ = _ := inv_diag (V:=V) h.inv i x

omit [∀ i, FiniteDimensional ℂ (V i)] in
private theorem diag_norm (A : BlockMatrix V) {K : ℝ} (hK : 0 ≤ K) (bound : ∀ x : X, ‖A x‖ ≤ K*‖x‖) (x : X) :
    ‖diagonalMap V A x‖ ≤ K * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg _))).mpr
  intro i
  calc
    _ ≤ ‖A (put V i (x i))‖ := norm_le_pi_norm _ i
    _ ≤ K*‖put V i (x i)‖ := bound _
    _ ≤ K*‖x‖ := mul_le_mul_of_nonneg_left ((put_norm_le V i (x i)).trans (norm_le_pi_norm x i)) hK

/-- The logarithmic payment for the off-diagonal change needs only bounded
relative frames and bounded relative inverses at the one fixed radius ratio. -/
theorem bounded (A : X ≃ₗ[ℂ] X) (h : triangular V A.toLinearMap) {K : ℝ} (hK : 0 ≤ K)
    (b : ∀ x : X, ‖A x‖ ≤ K*‖x‖ ∧ ‖A.symm x‖ ≤ K*‖x‖) (x : X) :
    ‖shear V A h x‖ ≤ K^2*‖x‖ ∧ ‖(shear V A h).symm x‖ ≤ K^2*‖x‖ := by
  constructor
  · change ‖A.symm (diagonalMap V A.toLinearMap x)‖ ≤ K^2*‖x‖
    refine (b _).2.trans ((mul_le_mul_of_nonneg_left (diag_norm V _ hK (fun v=>(b v).1) x) hK).trans_eq ?_)
    ring
  · change ‖diagonalMap V A.symm.toLinearMap (A x)‖ ≤ K^2*‖x‖
    refine (diag_norm V _ hK (fun v=>(b v).2) (A x)).trans ((mul_le_mul_of_nonneg_left (b x).1 hK).trans_eq ?_)
    ring

end YM.Integration.WilsonOrdinaryGradedShear
