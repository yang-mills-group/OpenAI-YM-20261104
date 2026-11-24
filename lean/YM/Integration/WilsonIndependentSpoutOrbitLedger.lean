import YM.Integration.WilsonIndependentSpoutRawRosterExit
/-! A fixed collection of signed orbit estimates supports every finite measured coefficient at its actual regulator. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOrbitLedger
open scoped BigOperators Classical
theorem original {T W:Type}[Fintype T](width tail:W→ℝ)(one:∀w,1≤width w)(positive:∀w,0≤tail w)
    (X Y:W→T→ℂ)(earned:∀i,∃k:ℕ,∃H:ℝ,0≤H ∧ ∀w,‖X w i-Y w i‖≤H*(width w)^k*tail w):
    ∃k:ℕ,∃H:ℝ,0≤H ∧ ∀(weight:W→T→ℂ)(w:W),
      ‖(∑i,weight w i*X w i)-(∑i,weight w i*Y w i)‖≤(∑i,‖weight w i‖)*(H*(width w)^k*tail w):=by
  choose k H nonnegative bill using earned
  refine ⟨∑i,k i,∑i,H i,Finset.sum_nonneg (fun i _=>nonnegative i),?_⟩
  intro weight w
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [←mul_sub,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (bill i w).trans (mul_le_mul_of_nonneg_right ?_ (positive w))
  exact mul_le_mul (Finset.single_le_sum (fun j _=>nonnegative j) hi)
    (pow_le_pow_right₀ (one w) (Finset.single_le_sum (fun j _=>Nat.zero_le (k j)) hi))
    (pow_nonneg (zero_le_one.trans (one w)) _) (Finset.sum_nonneg (fun j _=>nonnegative j))
end YM.Integration.WilsonIndependentSpoutOrbitLedger
