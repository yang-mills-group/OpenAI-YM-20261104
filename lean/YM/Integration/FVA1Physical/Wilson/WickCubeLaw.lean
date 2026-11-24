import YM.Integration.FVA1Physical.Wilson.WickTensorRecursion
import YM.Integration.FVA1Physical.Wilson.WickCubeTensors
import YM.Integration.FVA1Physical.Wilson.QuadraticResponse

/-! Dimension-independent expectation of every fixed-degree Taylor response
on the actual Gaussian, from its deterministic cube error and the covariance
row tariff. Every contraction uses the original covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Finset MeasureTheory Matrix Comparison.RG02 Comparison.RG02.Valence FVA1Physical.Round2
open YM.Next.SectorChange
open scoped BigOperators Classical ContDiff
variable {ι:Type} [Fintype ι] [DecidableEq ι]
local notation "V" => (ι→ℝ)

def cubeWickPrice (n:ℕ) (C A:ℝ):ℝ :=
  ∑ k:Fin (n+1),wickRent C k.val*(Contacts.Loom.poly_rent k.val).choose*(gridPrice n k/A^k.val)

theorem cubeWick_nonnegative (n:ℕ) {C A:ℝ} (hc:0≤C) (ha:0<A) : 0≤cubeWickPrice n C A := by
  apply sum_nonneg;intro k _
  exact mul_nonneg (mul_nonneg (wickRent_nonnegative hc _) (Contacts.Loom.poly_rent _).choose_spec.1)
    (div_nonneg (sum_nonneg fun _ _=>abs_nonneg _) (pow_pos ha _).le)

theorem real_wick_cube (K:Matrix ι ι ℝ) (pd:K.PosDef) {C A δ:ℝ}
    (hc:0≤C) (rows:∀i,∑ j,|K i j|≤C) (ha:0<A) {n:ℕ} {f:V→ℝ} (hf:Level n f)
    (cube:∀z,‖z‖≤A→‖f z‖≤δ) : |∫ z,f z ∂Gaussian.cloud K| ≤ cubeWickPrice n C A * δ := by
  let T:=fun (k:ℕ)=>Tensor.coeff f k 0
  have expand (z:V): f z=∑ k:Fin (n+1),Tensor.diagonal (T k.val) z := by
    rw [Fin.sum_univ_eq_sum_range (fun k:ℕ=>Tensor.diagonal (T k) z) (n+1)];exact hf.posted z
  rw [show f=fun z=>∑ k:Fin (n+1),Tensor.diagonal (T k.val) z from funext expand,
    integral_finsetSum _ (fun k _=>tensorIntegrable K pd (T k.val))]
  apply (abs_sum_le_sum_abs ..).trans
  unfold cubeWickPrice;rw [sum_mul];apply sum_le_sum;intro k _
  have base:=gaussian_tensor_bound K pd hc rows k.val (T k.val) (Tensor.coeff_symm (hf.smooth.contDiffAt.of_le (by simp)))
  have bill:=tensor_cube hf ha cube k
  exact (base.trans (mul_le_mul_of_nonneg_left bill (wickRent_nonnegative hc _))).trans_eq (by ring)

theorem complex_wick_cube (K:Matrix ι ι ℝ) (pd:K.PosDef) {C A δ:ℝ}
    (hc:0≤C) (rows:∀i,∑ j,|K i j|≤C) (ha:0<A) {n:ℕ} {f:V→ℂ} (hf:Level n f)
    (cube:∀z,‖z‖≤A→‖f z‖≤δ) : ‖∫ z,f z ∂Gaussian.cloud K‖ ≤ 2*cubeWickPrice n C A * δ := by
  by_cases ig:Integrable f (Gaussian.cloud K)
  · have re := real_wick_cube K pd hc rows ha (projected_degree hf Complex.reCLM)
      (fun z hz=>(Complex.abs_re_le_norm _).trans (cube z hz))
    have im := real_wick_cube K pd hc rows ha (projected_degree hf Complex.imCLM)
      (fun z hz=>(Complex.abs_im_le_norm _).trans (cube z hz))
    change |∫ z,Complex.reCLM (f z) ∂Gaussian.cloud K|≤_ at re
    change |∫ z,Complex.imCLM (f z) ∂Gaussian.cloud K|≤_ at im
    rw [Complex.reCLM.integral_comp_comm ig] at re;rw [Complex.imCLM.integral_comp_comm ig] at im
    exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add re im).trans_eq (by ring))
  · have hδ : 0≤δ := (norm_nonneg _).trans (cube 0 (by simpa using ha.le))
    rw [integral_undef ig,norm_zero];exact mul_nonneg (mul_nonneg (by norm_num) (cubeWick_nonnegative n hc ha)) hδ

end YM.Integration.FVA1Physical.Wilson.SignCovariance
