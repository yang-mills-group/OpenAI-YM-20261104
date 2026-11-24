import YM.Integration.WilsonOriginalSpatialProductRule

/-! The complete multilinear operator norm from all filed Cartesian lanes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiniteSpatialTensor
open Filter Finset
open WilsonOriginalSupportedBoxChart (Space)
open scoped ContDiff Classical BigOperators

theorem original {d j : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => Space d) ℂ)
    {B : ℝ} (pos : 0 ≤ B) (paid : ∀ i : Fin j → Fin d, ‖M (fun k => Pi.single (i k) (1:ℝ))‖ ≤ B) :
    ‖M‖ ≤ (d:ℝ)^j*B := by
  apply M.opNorm_le_bound (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) pos)
  intro m
  have expand (k : Fin j) : (∑ i : Fin d, (m k i) • Pi.single i (1:ℝ)) = m k := by
    funext t
    simp [Finset.sum_apply,Pi.single_apply]
  rw [show m = fun k => ∑ i : Fin d, (m k i) • Pi.single i (1:ℝ) from funext fun k => (expand k).symm]
  rw [M.map_sum]
  simp only [expand]
  apply (norm_sum_le ..).trans
  calc
    ∑ i : Fin j → Fin d, ‖M (fun k => (m k (i k)) • Pi.single (i k) (1:ℝ))‖ ≤
        ∑ _ : Fin j → Fin d, (∏ k, ‖m k‖)*B := by
      apply sum_le_sum
      intro i _
      rw [M.map_smul_univ,norm_smul,norm_prod]
      exact mul_le_mul (prod_le_prod (fun _ _ => norm_nonneg _)
        (fun k _ => norm_le_pi_norm (m k) (i k))) (paid i) (norm_nonneg _) (by positivity)
    _ = (d:ℝ)^j*B*∏ k, ‖m k‖ := by simp; ring

end YM.Integration.WilsonOriginalFiniteSpatialTensor
