import YM.Integration.WilsonIndependentReportedPhysicalTable

/-! Contract the measured signed columns and restore the original report clock after the stopping comparison. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalSignedClock
open RegulatorIR.Profiles RegulatorIR.Calibration WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonIndependentPublicReportComplex (row)
open scoped Classical BigOperators PowerSeries

theorem column (K:Feeds)(D q:ℕ)(A B:PowerSeries ℂ)(cost:ℕ → ℝ)
    (paid:∀i,i≤q → ‖PowerSeries.coeff i A-PowerSeries.coeff i B‖≤cost i):
    ‖PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply K D A)-
      PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply K D B)‖≤
      ∑i∈Finset.range (q+1),cost i*‖row K D q i‖:=by
  rw [WilsonIndependentPublicReportComplex.difference]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (paid i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (norm_nonneg _)

theorem roster {I:Type}[Fintype I](K:Feeds)(D q:ℕ)(c:I → ℂ)(A B:I → PowerSeries ℂ)(cost:I → ℕ → ℝ)
    (paid:∀a i,i≤q → ‖PowerSeries.coeff i (A a)-PowerSeries.coeff i (B a)‖≤cost a i):
    ‖PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply K D (∑a,PowerSeries.C (c a)*A a))-
      PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply K D (∑a,PowerSeries.C (c a)*B a))‖≤
      ∑a,‖c a‖*∑i∈Finset.range (q+1),cost a i*‖row K D q i‖:=by
  rw [WilsonIndependentReportedPhysicalTable.linear,WilsonIndependentReportedPhysicalTable.linear,
    ←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (column K D q (A a) (B a) (cost a) (paid a)) (norm_nonneg _)

theorem test {I Z:Type}[Fintype I][Fintype Z](K:Z → Feeds)(D q:ℕ)(ν:Z → ℂ)(c:Z → I → ℂ)
    (A B:Z → I → PowerSeries ℂ)(cost:Z → I → ℕ → ℝ)
    (paid:∀z a i,i≤q → ‖PowerSeries.coeff i (A z a)-PowerSeries.coeff i (B z a)‖≤cost z a i):
    ‖∑z,ν z*(PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (K z) D (∑a,PowerSeries.C (c z a)*A z a))-
      PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (K z) D (∑a,PowerSeries.C (c z a)*B z a)))‖≤
      ∑z,‖ν z‖*(∑a,‖c z a‖*∑i∈Finset.range (q+1),cost z a i*‖row (K z) D q i‖):=by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (roster (K z) D q (c z) (A z) (B z) (cost z) (paid z)) (norm_nonneg _)

end YM.Integration.WilsonOriginalPublicNodalSignedClock
end
