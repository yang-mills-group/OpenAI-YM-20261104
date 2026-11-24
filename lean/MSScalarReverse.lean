import MSScalarInverse
import Mathlib.RingTheory.PowerSeries.Substitution

/-! The scalar inverse cancels the detector in either order of composition. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section

namespace YangMills.MSbar.Series

open Matching (couplingPower)
open PowerSeries
open scoped BigOperators

private theorem power_coeff (a : ℕ → ℝ) (j k : ℕ) :
    coeff k (mk a ^ j) = couplingPower a j k := by
  induction j generalizing k with
  | zero => simp only [pow_zero, coeff_one, couplingPower]
  | succ j ih =>
    rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun l r => coeff l (mk a) * coeff r (mk a ^ j)), couplingPower]
    simp only [coeff_mk, ih]
    exact (Fin.sum_univ_eq_sum_range (fun i => a i * couplingPower a j (k-i)) (k+1)).symm

private theorem subst_coeff (a b : ℕ → ℝ) (hb : b 0 = 0) (k : ℕ) :
    coeff k ((mk a).subst (mk b)) = ∑ j ∈ Finset.range (k+1), a j * couplingPower b j k := by
  have hb' : constantCoeff (mk b) = 0 := by simpa [← coeff_zero_eq_constantCoeff_apply] using hb
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hb')]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (k+1))]
  · simp only [coeff_mk, smul_eq_mul, power_coeff]
  · intro j hj
    by_contra h
    have hkj : k < j := by simpa using h
    have hz := coeff_of_lt_order k ((Nat.cast_lt.mpr hkj).trans_le
      (le_order_pow_of_constantCoeff_eq_zero j hb'))
    exact hj (by simp [hz])

private theorem reverse_subst (P F : PowerSeries ℝ) (hP : constantCoeff P = 0)
    (hF : constantCoeff F = 0) (hu : IsUnit (coeff 1 P)) (hPF : P.subst F = X) :
    F.subst P = X := by
  have hp : HasSubst P := HasSubst.of_constantCoeff_zero' hP
  have hf : HasSubst F := HasSubst.of_constantCoeff_zero' hF
  let Q := P.substInvOfIsUnit hu
  have hQP : Q.subst P = X := P.subst_substInvOfIsUnit_left hP hu
  have hFQ : F = Q := calc
    F = PowerSeries.subst F (Q.subst P) := by rw [hQP, subst_X hf]
    _ = Q.subst (P.subst F) := subst_comp_subst_apply hp hf Q
    _ = Q := by rw [hPF, X_subst]
  exact (congrArg (fun R : PowerSeries ℝ => R.subst P) hFQ).trans hQP

/-- The triangular inverse composed with the original detector equals the identity series. -/
theorem inverse_after_coupling (χ : ℕ → ℝ) (h₀ : χ 0 = 0) (h₁ : χ 1 = 1) (k : ℕ) :
    (∑ j ∈ Finset.range (k+1), inverseCoupling χ j * couplingPower χ j k) =
      if k = 1 then 1 else 0 := by
  let f := inverseCoupling χ
  have hf : f 0 = 0 := inverseCoupling_zero χ
  have hP : constantCoeff (mk χ) = 0 := by simpa [← coeff_zero_eq_constantCoeff_apply] using h₀
  have hF : constantCoeff (mk f) = 0 := by simpa [← coeff_zero_eq_constantCoeff_apply] using hf
  have hu : IsUnit (coeff 1 (mk χ)) := by simp [h₁]
  have hPF : (mk χ).subst (mk f) = X := PowerSeries.ext fun n =>
    (subst_coeff χ f hf n).trans ((coupling_after_inverse χ h₀ h₁ n).trans (coeff_X n).symm)
  exact (subst_coeff f χ h₀ k).symm.trans
    ((congrArg (coeff k) (reverse_subst _ _ hP hF hu hPF)).trans (coeff_X k))

end YangMills.MSbar.Series
