import YM.Integration.FVA1Physical.Wilson.ResetGrid
import YM.Contacts.Loom.Iris

/-! Universal-norm bound on every real Taylor coefficient of a bounded
finite-degree response on a deterministic cube. The Vandermonde inversion
and polarization tariff are fixed before the lattice or field dimension. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Finset Analysis Comparison.RG02 Comparison.RG02.Valence FVA1Physical.Round2
open scoped Classical BigOperators ContDiff
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem real_row {f:X→ℝ} {n:ℕ} (hf:Level n f) (x:X) (i:Fin (n+1)) :
    Assembly.jet f i.val x = ∑ j,gridCoeff n i j*f (unitGrid n j • x) := by
  let M := Matrix.vandermonde (unitGrid n)
  have invert : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,Matrix.det_vandermonde_ne_zero_iff];intro j k e
    have eq : (j.val:ℝ)/((n:ℝ)+1) = (k.val:ℝ)/((n:ℝ)+1) := e
    apply Fin.ext;exact_mod_cast (div_left_inj' (show (n:ℝ)+1≠0 by positivity)).mp eq
  let v (k:Fin (n+1)) := Assembly.jet f k.val x
  have nodes (j:Fin (n+1)) : f (unitGrid n j • x) = ∑ k, M j k * v k := by
    rw [hf.posted]
    change _ = ∑ k:Fin (n+1), unitGrid n j ^ k.val * Assembly.jet f k.val x
    rw [Fin.sum_univ_eq_sum_range (fun k:ℕ=> unitGrid n j ^ k * Assembly.jet f k x) (n+1)]
    exact sum_congr rfl fun k _=>Assembly.Clipper.weight x (unitGrid n j) k f
  simp_rw [nodes];change v i = ∑ j,M⁻¹ i j * ∑ k,M j k * v k
  simp only [mul_sum,←mul_assoc];rw [sum_comm]
  simp only [←sum_mul,←Matrix.mul_apply,Matrix.nonsing_inv_mul M invert];simp [Matrix.one_apply]

/-- Uniform in the ambient real normed space, before all choices of test directions. -/
theorem tensor_cube {f:X→ℝ} {n:ℕ} (hf:Level n f) {A δ:ℝ} (ha:0<A)
    (cube:∀x,‖x‖≤A→‖f x‖≤δ) (i:Fin (n+1)) :
    ‖Tensor.coeff f i.val 0‖ ≤ (Contacts.Loom.poly_rent i.val).choose*(gridPrice n i * δ/A^i.val) := by
  have gδ:0≤δ:=(norm_nonneg _).trans (cube 0 (by simpa using ha.le))
  have gprice:0≤gridPrice n i:=sum_nonneg fun _ _=>abs_nonneg _
  have bound(x:X)(hx:‖x‖≤A):‖Assembly.jet f i.val x‖≤gridPrice n i*δ := by
    rw [real_row hf];apply (norm_sum_le ..).trans
    calc _ ≤ ∑ j,|gridCoeff n i j| *δ := sum_le_sum fun j _=>by
           rw [norm_mul,Real.norm_eq_abs];apply mul_le_mul_of_nonneg_left _ (abs_nonneg _);apply cube
           rw [norm_smul,Real.norm_of_nonneg (unitGrid_mem n j).1];exact (mul_le_of_le_one_left (norm_nonneg x) (unitGrid_mem n j).2).trans hx
         _ = _ := (sum_mul ..).symm
  apply (Contacts.Loom.poly_rent i.val).choose_spec.2 _ _ (Tensor.coeff_symm (hf.smooth.contDiffAt.of_le (by simp))) _ (div_nonneg (mul_nonneg gprice gδ) (pow_pos ha _).le)
  intro x
  let u:=(‖x‖⁻¹:ℝ) • x
  have normU:‖u‖≤1 := by
    by_cases h:x=0
    · simp [u,h]
    · rw [show ‖u‖=‖(‖x‖⁻¹:ℝ)‖*‖x‖ from norm_smul ..,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]
  have undo:‖x‖ • u=x := by
    by_cases h:x=0
    · simp [u,h]
    · rw [show ‖x‖ • u=(‖x‖*‖x‖⁻¹) • x from smul_smul ..,mul_inv_cancel₀ (norm_ne_zero_iff.mpr h),one_smul]
  have inner:=bound (A • u) (by rw [norm_smul,Real.norm_of_nonneg ha.le];exact mul_le_of_le_one_right ha.le normU)
  rw [Assembly.Clipper.weight,norm_smul,Real.norm_of_nonneg (pow_pos ha _).le] at inner
  have unit:‖Assembly.jet f i.val u‖≤gridPrice n i*δ/A^i.val := (le_div_iff₀ (pow_pos ha _)).mpr ((mul_comm ..).le.trans inner)
  change ‖Assembly.jet f i.val x‖≤_
  calc _ = ‖Assembly.jet f i.val (‖x‖ • u)‖ := by rw [undo]
       _ = (‖x‖^i.val)*‖Assembly.jet f i.val u‖ := by rw [Assembly.Clipper.weight,norm_smul,Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
       _ ≤ _ := ((mul_le_mul_of_nonneg_left unit (pow_nonneg (norm_nonneg _) _)).trans_eq (mul_comm ..))

end YM.Integration.FVA1Physical.Wilson.SignCovariance
