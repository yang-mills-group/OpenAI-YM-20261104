import YM.Integration.FVA1Physical.Round2.FieldDerivativeCost

/-! Pay the discarded coefficient rows and dimension-free differentiation
constant with an arbitrarily small loss of the measured coupling exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter
open scoped Topology

def rowExponent (η:ℝ) := min (η/4) (1/2:ℝ)

theorem derivative_clock (p:ℕ) (C d:ℝ) (hd:0≤d) {η:ℝ} (he:0<η) :
    0<rowExponent η ∧ ∀ᶠ β:ℝ in atTop,∀ x:ℝ,1≤x → x≤2*β →
      x^(rowExponent η) ≤ β ∧
      (C+d*x^(rowExponent η))*((Real.sqrt β)⁻¹)^(p+1) ≤ ((Real.sqrt β)⁻¹)^((p:ℝ)+1-η) := by
  let δ:=rowExponent η
  have pos:0<δ:=lt_min (by linarith only [he]) (by norm_num)
  have gap:0<η/2-δ:=by have h:δ≤η/4:=min_le_left ..;linarith only [he,h]
  let M:=|C|+d*(2:ℝ)^δ
  refine ⟨pos,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),(tendsto_rpow_atTop gap).eventually_ge_atTop M] with β large cap
  intro x hx upper
  have hβ:0<β:=lt_of_lt_of_le (by norm_num) large
  have β1:1≤β:=one_le_two.trans large
  have H:x^δ≤(2*β)^δ:=Real.rpow_le_rpow (zero_le_one.trans hx) upper pos.le
  have root : Real.sqrt (2*β) ≤ β := (Real.sqrt_le_left hβ.le).mpr (by nlinarith only [mul_nonneg hβ.le (sub_nonneg.mpr large)])
  refine ⟨H.trans ((Real.rpow_le_rpow_of_exponent_le (by linarith only [large]) (min_le_right ..)).trans_eq
    (Real.sqrt_eq_rpow (2*β)).symm) |>.trans root,?_⟩
  rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) hβ.le] at H
  have paid:C+d*x^δ≤β^(η/2):=calc
    _ ≤ M*β^δ := by
      unfold M
      rw [add_mul,mul_assoc]
      have left : C ≤ |C| * β^δ := (le_abs_self _).trans
        (le_mul_of_one_le_right (abs_nonneg C) (Real.one_le_rpow β1 pos.le))
      exact add_le_add left (mul_le_mul_of_nonneg_left H hd)
    _ ≤ β^(η/2-δ)*β^δ := mul_le_mul_of_nonneg_right cap (Real.rpow_nonneg hβ.le _)
    _ = _ := by rw [←Real.rpow_add hβ,sub_add_cancel]
  let g:=(Real.sqrt β)⁻¹
  have hg:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have same:g^(-η)=β^(η/2):=by
    dsimp only [g]
    rw [Real.sqrt_eq_rpow,←Real.rpow_neg hβ.le,←Real.rpow_mul hβ.le]
    congr 1;ring
  change (C+d*x^δ)*g^(p+1) ≤ g^((p:ℝ)+1-η)
  apply (mul_le_mul_of_nonneg_right (paid.trans_eq same.symm) (pow_nonneg hg.le _)).trans_eq
  rw [←Real.rpow_natCast g (p+1),←Real.rpow_add hg]
  push_cast
  congr 1;ring

end YM.Integration.FVA1Physical.Round2.Curvature
