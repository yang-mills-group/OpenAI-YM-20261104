import YM.RGComparison.Core16.Normalize

/-! The first differing term in two ratios with the same leading denominator.
Every coefficient common to the two books may be nonzero. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalDivision
open PowerSeries
open scoped Classical BigOperators
abbrev Series := PowerSeries ℝ
def zeroBefore (A : Series) (w : ℕ) := ∀ k < w, coeff k A = 0

theorem productLower {A B : Series} {a b : ℕ} (ha : zeroBefore A a) (hb : zeroBefore B b) :
    zeroBefore (A*B) (a+b) := by
  intro i hi
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro j hj
  have sum := Finset.mem_antidiagonal.mp hj
  by_cases low : j.1 < a
  · rw [ha _ low,zero_mul]
  · rw [hb j.2 (by omega),mul_zero]

theorem productFirst {A B : Series} {a b : ℕ} (ha : zeroBefore A a) (hb : zeroBefore B b) :
    coeff (a+b) (A*B) = coeff a A * coeff b B := by
  rw [coeff_mul]
  apply Finset.sum_eq_single_of_mem (a,b) (Finset.mem_antidiagonal.mpr rfl)
  intro j hj different
  have sum := Finset.mem_antidiagonal.mp hj
  by_cases low : j.1 < a
  · rw [ha _ low,zero_mul]
  · rw [hb j.2 (by by_contra late; apply different; ext <;> omega),mul_zero]

private theorem zeroNone (A : Series) : zeroBefore A 0 := by intro k hk; omega

/-- A graded observed series first changes by its numerator change minus the
already normalized leading field times the actual vacuum change. -/
theorem changed {N U V D : Series} {w : ℕ} (d0 : coeff 0 D ≠ 0) (v0 : coeff 0 V ≠ 0)
    (old : zeroBefore N w) (inputs : zeroBefore (U-N) (w+2)) (vacua : zeroBefore (D-V) 2) :
    coeff (w+2) (U*D⁻¹ - N*V⁻¹) =
      (coeff (w+2) (U-N) - (coeff w N / coeff 0 V) * coeff 2 (D-V)) / coeff 0 D := by
  have d := PowerSeries.mul_inv_cancel D (by simpa only [← coeff_zero_eq_constantCoeff_apply] using d0)
  have v := PowerSeries.mul_inv_cancel V (by simpa only [← coeff_zero_eq_constantCoeff_apply] using v0)
  let O := N*V⁻¹
  have hO : zeroBefore O w := by simpa only [Nat.add_zero] using productLower old (zeroNone V⁻¹)
  let A := (U-N) - O*(D-V)
  have hA : zeroBefore A (w+2) := by
    intro i hi
    rw [show coeff i A = _ - _ from map_sub .., inputs i hi, productLower hO vacua i hi,sub_zero]
  have h : U*D⁻¹ - N*V⁻¹ = A*D⁻¹ := by
    have Oeq : O*V=N := by dsimp [O]; rw [mul_assoc,mul_comm V⁻¹ V,v,mul_one]
    have aeq : A = U-O*D := by dsimp only [A]; rw [mul_sub,Oeq]; ring
    rw [aeq,sub_mul,mul_assoc,d,mul_one]
  have Ocoeff : coeff w O = coeff w N / coeff 0 V := by
    have h := productFirst old (zeroNone V⁻¹)
    simpa only [O,Nat.add_zero,coeff_zero_eq_constantCoeff_apply,constantCoeff_inv,div_eq_mul_inv] using h
  rw [h, ← Nat.add_zero (w+2),productFirst hA (zeroNone D⁻¹), Nat.add_zero]
  simp only [A,map_sub, productFirst hO vacua,Ocoeff,coeff_zero_eq_constantCoeff_apply,constantCoeff_inv,
    div_eq_mul_inv]

end YM.Integration.WilsonConditionalTaylorThermalDivision
