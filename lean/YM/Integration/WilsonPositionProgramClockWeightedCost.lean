import YM.Integration.WilsonPositionProgramDatedClockBill

noncomputable section
namespace YM.Integration.WilsonPositionProgramClockWeightedCost
open Finset Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Moving.Path WilsonPositionProgramDatedClockBill
open scoped Classical BigOperators

theorem original (T : UnitCost) (d : ℤ) (r k : ℕ) (h : ℕ → ℕ) (u v : ℕ → ℕ → ℝ)
    (C D : ℝ) (paid : ∀a ≤ r,∀b ≤ h a,C*u a b ≤ D*v a b) :
    C*cost T d r k h u ≤ D*cost T d r k h v := by
  simp only [cost, mul_sum]
  refine sum_le_sum fun a ha=>sum_le_sum fun j _=>sum_le_sum fun b hb=>?_
  have accepted := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (paid a (mem_range_succ_iff.mp ha) b (mem_range_succ_iff.mp hb))
      (norm_nonneg (WilsonPositionProgramRadialPrices.factor (h a) j b)))
    (norm_nonneg (motion (money T d a j) k))
  simpa only [mul_left_comm C, mul_left_comm D] using accepted

end YM.Integration.WilsonPositionProgramClockWeightedCost
end
