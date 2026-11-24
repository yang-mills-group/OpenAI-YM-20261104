import YM.Integration.WilsonConditionalTaylorThermalNextProduct

/-! The actual previous normalized source and both unmarked coefficients
in the next variation of a quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalInteractionDivision
open PowerSeries WilsonConditionalTaylorThermalDivision
open scoped Classical BigOperators
variable {N U V D : PowerSeries ℝ} {w : ℕ}

private theorem free (A : PowerSeries ℝ) : zeroBefore A 0 := by intro k h; omega

theorem normalized (v : coeff 0 V ≠ 0) : (N*V⁻¹)*V=N := by
  have e := PowerSeries.mul_inv_cancel V (by simpa only [←coeff_zero_eq_constantCoeff_apply] using v)
  rw [mul_assoc,mul_comm V⁻¹ V,e,mul_one]

theorem incoming (v : coeff 0 V ≠ 0) (old : zeroBefore (N*V⁻¹) w) :
    coeff w (N*V⁻¹)*coeff 0 V=coeff w N ∧
    coeff w (N*V⁻¹)*coeff 1 V+coeff (w+1) (N*V⁻¹)*coeff 0 V=coeff (w+1) N := by
  have h := normalized (N:=N) v
  constructor
  · have e := productFirst old (free V)
    simpa only [Nat.add_zero,h] using e.symm
  · have e := WilsonConditionalTaylorThermalNextProduct.series old (free V)
    simpa only [Nat.add_zero,Nat.zero_add,h] using e.symm

theorem differing (d0 : coeff 0 D ≠ 0) (v : coeff 0 V ≠ 0)
    (old : zeroBefore (N*V⁻¹) w) (early : zeroBefore (U*D⁻¹-N*V⁻¹) (w+2))
    (vacua : zeroBefore (D-V) 2) :
    coeff (w+2) (U*D⁻¹-N*V⁻¹)*coeff 1 D +
    coeff (w+3) (U*D⁻¹-N*V⁻¹)*coeff 0 D +
    (coeff w (N*V⁻¹)*coeff 3 (D-V)+coeff (w+1) (N*V⁻¹)*coeff 2 (D-V)) =
      coeff (w+3) (U-N) := by
  let A := U*D⁻¹
  let B := N*V⁻¹
  have eq : (A-B)*D+B*(D-V)=U-N := by
    rw [sub_mul,mul_sub,show A*D=U from normalized d0,show B*V=N from normalized v]
    ring
  have price := congrArg (coeff (w+3) (R:=ℝ)) eq
  rw [map_add] at price
  have left := WilsonConditionalTaylorThermalNextProduct.series early (free D)
  have right := WilsonConditionalTaylorThermalNextProduct.series old vacua
  simpa only [Nat.add_zero,Nat.zero_add] using
    (left.symm ▸ right.symm ▸ price : _)

end YM.Integration.WilsonConditionalTaylorThermalInteractionDivision
