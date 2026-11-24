import Mathlib.Analysis.Normed.Operator.Basic
import YM.Integration.WilsonLinearKernelFactor

/-! Exact cancellation of the linear matrix displacement under inversion of the Wilson noise. -/
noncomputable section
namespace YM.Integration.WilsonMatrixInversion
open YM RG Lattice Wilson MeasureTheory
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open WilsonKernelCoupling
variable (G : Gauge)

theorem square (g : G.El) : ‖G.mat g-1‖^2 = (G.repDim:ℝ)*(2*G.price g) := by
  have hd : 0 < (G.repDim:ℝ) := by exact_mod_cast G.dimPos
  have h := G.chord_price g
  unfold Gauge.chord at h
  rw [div_pow,Real.sq_sqrt hd.le,div_eq_iff hd.ne'] at h
  rwa [mul_comm]

theorem opposite (g : G.El) : ‖1-G.mat g⁻¹‖ = ‖G.mat g-1‖ := by
  rw [norm_sub_rev]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [square,square,G.price_inv]

theorem probe_bound (B : G.Mat →L[ℝ] ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x, ‖B x‖ ≤ L*‖x‖ :=
  SemilinearMapClass.bound_of_continuous (B : G.Mat →ₗ[ℝ] ℝ) B.continuous

theorem secant (B : G.Mat →L[ℝ] ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hB : ∀ x, ‖B x‖ ≤ L*‖x‖) (g q : G.El) :
    |B (G.mat (g*q)) + B (G.mat (g⁻¹*q)) - 2*B (G.mat q)| ≤
       2*(G.repDim:ℝ)*L*G.price g := by
  have hprod : G.mat g * G.mat g⁻¹ = 1 := by
    rw [← G.mat_mul,mul_inv_cancel,G.mat_one]
  have hdiff : (G.mat g-1)*(1-G.mat g⁻¹)=(G.mat g-1)+(G.mat g⁻¹-1) := by
    rw [sub_mul,mul_sub,mul_one,hprod,one_mul]
    abel
  have he : B (G.mat (g*q)) + B (G.mat (g⁻¹*q)) - 2*B (G.mat q) =
      B (((G.mat g-1)*(1-G.mat g⁻¹))*G.mat q) := by
    rw [hdiff,add_mul,sub_mul,sub_mul,one_mul]
    simp only [map_add,map_sub,G.mat_mul]
    ring
  rw [he,← Real.norm_eq_abs]
  calc
    _ ≤ L*‖((G.mat g-1)*(1-G.mat g⁻¹))*G.mat q‖ := hB _
    _ = L*‖(G.mat g-1)*(1-G.mat g⁻¹)‖ := by rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star q)]
    _ ≤ L*(‖G.mat g-1‖*‖1-G.mat g⁻¹‖) := mul_le_mul_of_nonneg_left (norm_mul_le ..) hL
    _ = _ := by rw [opposite,← sq,square]; ring

end YM.Integration.WilsonMatrixInversion
