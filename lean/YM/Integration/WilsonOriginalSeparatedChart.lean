import YM.Integration.WilsonOriginalAffineShapeJets

/-! An actual small Cartesian box around each separated physical configuration.
Its linear part is invertible and each column has norm at most one. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSeparatedChart
open Set Metric
open scoped Topology Classical

theorem original {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (e : (Fin d → ℝ) ≃L[ℝ] E) {O : Set E} (opn : IsOpen O) {x : E} (hx : x ∈ O) :
    ∃ (a : E) (L : (Fin d → ℝ) ≃L[ℝ] E), (∀ i : Fin d, ‖L (Pi.single i (1:ℝ))‖ ≤ 1) ∧
      (∀ z : Fin d → ℝ, (∀ i, z i ∈ Icc (0:ℝ) 1) → a + L z ∈ O) ∧
      a + L (fun _ => (1/2:ℝ)) = x := by
  obtain ⟨R,hR,tube⟩ := Metric.isOpen_iff.mp opn x hx
  let c := (min (1:ℝ) R)/(2*(1+‖e.toContinuousLinearMap‖))
  have cp : 0 < c := div_pos (lt_min one_pos hR) (by positivity)
  let L := (Units.mk0 c cp.ne') • e
  let mid := fun _ : Fin d => (1/2:ℝ)
  have small : c*‖e.toContinuousLinearMap‖ ≤ min 1 R/2 := by
    have sal : c*(2*(1+‖e.toContinuousLinearMap‖)) = min 1 R :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [cp.le]
  have budget (z : Fin d → ℝ) (norm : ‖z‖ ≤ 1) : ‖L z‖ ≤ min 1 R/2 := by
    change ‖c • e z‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos cp]
    exact (mul_le_mul_of_nonneg_left
      ((e.toContinuousLinearMap.le_opNorm z).trans
        ((mul_le_mul_of_nonneg_left norm (norm_nonneg _)).trans_eq (mul_one _))) cp.le).trans small
  refine ⟨x-L mid,L,fun i => (budget _ (by rw [Pi.norm_single,norm_one])).trans (by linarith [min_le_left (1:ℝ) R]),?_,sub_add_cancel _ _⟩
  intro z cube
  have debit : ‖z-mid‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by
    rw [Real.norm_eq_abs, abs_le]
    change -(1:ℝ) ≤ z i - 1/2 ∧ z i - 1/2 ≤ 1
    constructor <;> linarith [(cube i).1,(cube i).2]
  apply tube
  rw [mem_ball,dist_eq_norm,show x-L mid+L z-x = L (z-mid) by rw [map_sub]; abel]
  exact (budget _ debit).trans_lt (by linarith [min_le_right (1:ℝ) R])

end YM.Integration.WilsonOriginalSeparatedChart
