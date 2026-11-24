import YM.Integration.WilsonReportingAbsoluteInletForecastBooks

/-! A before-date bound on the absolute coefficients of the formal inverse,
using only the filed positive-order coefficients of the same kinetic book. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastCapital
open Finset PowerSeries FormalBulk08.Wine WilsonReportingAbsoluteInletForecastBooks
theorem control (D:PowerSeries ℝ) (n:ℕ) {M:ℝ} (M0:0 ≤ M)
    (cap:∀i,i ≤ n→|coeff i (bookU D)| ≤ M):
    mass n (bookU D) ≤ (n+1)*M ∧ mass n (bookH D) ≤ (1+M)^n:=by
  let H:=bookH D
  let U:=bookU D
  have money:=WilsonReportingAbsoluteInletForecastBooks.exact D
  have first:coeff 0 U=1:=money.1
  have head:coeff 0 H=1:=money.2.1
  have whole:H*U=1:=money.2.2
  have next (k:ℕ)(keep:k+1 ≤ n):|coeff (k+1) H| ≤ mass k H*M:=by
    have zero:coeff (k+1) (H*U)=0:=by simp [whole, PowerSeries.coeff_one]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      Nat.sub_self,first,mul_one] at zero
    have neg:coeff (k+1) H= -(∑i∈range (k+1),coeff i H*coeff (k+1-i) U):=by linarith
    rw [neg,abs_neg]
    calc
      _ ≤ ∑i∈range (k+1),|coeff i H*coeff (k+1-i) U|:=Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑i∈range (k+1),|coeff i H| *M:=by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (cap _ (by omega)) (abs_nonneg _)
      _ = mass k H*M:=by rw [mass,Finset.sum_mul]
  have saved (k:ℕ)(keep:k ≤ n):mass k H ≤ (1+M)^k:=by
    induction k with
    | zero => simp [mass,head]
    | succ k ih =>
      have prev:=ih (by omega)
      have edge:=next k keep
      have add : mass (k+1) H=mass k H+|coeff (k+1) H|:=by rw [mass,Finset.sum_range_succ];rfl
      calc
        mass (k+1) H ≤ mass k H + mass k H*M:=by rw [add]; linarith
        _ = mass k H*(1+M):=by ring
        _ ≤ (1+M)^k*(1+M):=mul_le_mul_of_nonneg_right prev (by linarith)
        _ = _ := (pow_succ _ _).symm
  refine ⟨?_,saved n le_rfl⟩
  calc
    mass n (bookU D) ≤ ∑i∈range (n+1),M:=by
      apply Finset.sum_le_sum
      intro i hi
      exact cap i (by have:=mem_range.mp hi;omega)
    _ = (n+1)*M:=by simp
end YM.Integration.WilsonReportingAbsoluteInletForecastCapital
