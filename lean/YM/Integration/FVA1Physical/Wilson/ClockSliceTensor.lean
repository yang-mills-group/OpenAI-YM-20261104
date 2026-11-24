import YM.Integration.FVA1Physical.Wilson.ClockSlicePrice

/-! The scalar painter on its physical unit-clock field ball pays every
mixed, independently tested component of the full clock-field Taylor tensor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Comparison.RG02 Assembly
open scoped Classical ContDiff BigOperators
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem complex_diagonal_charge {k:ℕ} (T:Tensor.T X ℂ k) (sym:Tensor.Sym T)
    {δ:ℝ} (cap:∀x:X,‖x‖≤1→‖Tensor.diagonal T x‖≤δ):
    ‖T‖ ≤ 2*(Contacts.Loom.poly_rent k).choose*δ:=by
  have d0:0≤δ:=(norm_nonneg _).trans (cap 0 (by simp))
  let u:=(Contacts.Loom.poly_rent k).choose
  have u0:0≤u:=(Contacts.Loom.poly_rent k).choose_spec.1
  have diag(x:X):‖Tensor.diagonal T x‖≤δ*‖x‖^k:=by
    let y:=(‖x‖⁻¹:ℝ) • x
    have yn:‖y‖≤1:=by
      by_cases hx:x=0
      · simp [y,hx]
      rw [show ‖y‖=‖(‖x‖⁻¹:ℝ)‖*‖x‖ from norm_smul ..,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have undo:‖x‖ • y=x:=by
      by_cases hx:x=0
      · simp [y,hx]
      rw [show ‖x‖ • y=(‖x‖*‖x‖⁻¹) • x from smul_smul ..,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]
    calc _ = ‖Tensor.diagonal T (‖x‖ • y)‖:=by rw [undo]
         _ = ‖x‖^k*‖Tensor.diagonal T y‖:=by rw [Tensor.homogeneous,norm_smul,Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
         _ ≤ _ := (mul_le_mul_of_nonneg_left (cap y yn) (pow_nonneg (norm_nonneg _) _)).trans_eq (mul_comm ..)
  have component (L:ℂ→L[ℝ]ℝ) (contract:∀ z,‖L z‖≤‖z‖):
      ‖L.compContinuousMultilinearMap T‖≤u*δ:=by
    apply (Contacts.Loom.poly_rent k).choose_spec.2
    · intro v σ;exact congrArg L (sym v σ)
    · exact d0
    intro x;exact (contract _).trans (diag x)
  have real:=component Complex.reCLM (fun z=>(Complex.abs_re_le_norm z))
  have imag:=component Complex.imCLM (fun z=>(Complex.abs_im_le_norm z))
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have budget(L:ℂ→L[ℝ]ℝ) (p:‖L.compContinuousMultilinearMap T‖≤u*δ):‖L (T v)‖≤u*δ*∏i,‖v i‖:=
    ((L.compContinuousMultilinearMap T).le_opNorm v).trans (mul_le_mul_of_nonneg_right p (Finset.prod_nonneg fun _ _=>norm_nonneg _))
  exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add (budget _ real) (budget _ imag)).trans_eq (by change _=2*u*δ*_;ring))

theorem clock_slice_tensor {a b:ℝ×X→ℂ} (sa:ContDiffAt ℝ ω a 0) (sb:ContDiffAt ℝ ω b 0)
    (k:ℕ) {δ:ℝ} (slice:∀u:X,‖u‖≤1→‖jet a k (1,u)-jet b k (1,u)‖≤δ):
    ‖Tensor.coeff a k 0-Tensor.coeff b k 0‖≤
      2*(Contacts.Loom.poly_rent k).choose*(clockRent k*δ) := by
  apply complex_diagonal_charge
  · intro v σ;rw [_root_.sub_apply,_root_.sub_apply,Tensor.coeff_symm (sa.of_le le_top) v σ,Tensor.coeff_symm (sb.of_le le_top) v σ]
  intro x hx
  exact unit_clock_cube sa sb k slice x hx
end YM.Integration.FVA1Physical.Wilson
