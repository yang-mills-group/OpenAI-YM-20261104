import YM.Integration.WilsonIndependentWardStampOrbit

/-! Combine finitely many genuine termwise period prices after coefficient
extraction. The variable absolute coefficient sum is restored only once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardFiniteBudget
open scoped Classical BigOperators
variable {I ι:Type}[Fintype ι]

theorem original (mod rate:I→ℝ)(large:∀w,1 ≤ mod w)(pos:∀w,0≤rate w)
    (F:ι→I→ℝ)(price:∀i,∃C:ℝ,∃k:ℕ,0≤C ∧ ∀w,‖F i w‖ ≤ C * (mod w)^k * rate w) :
    ∃C:ℝ,∃k:ℕ,0≤C ∧ ∀(c:I→ι→ℝ)(M:I→ℝ), (∀w,(∑ i,‖c w i‖)≤M w) →
      ∀w,‖∑ i,c w i * F i w‖ ≤ M w * (C*(mod w)^k*rate w) := by
  choose C k hC hp using price
  refine ⟨∑ i,C i,∑ i,k i,Finset.sum_nonneg (fun i _=>hC i),?_⟩
  intro c M cash w
  have payment(i:ι):‖F i w‖≤(∑ j,C j)*(mod w)^(∑ j,k j)*rate w := by
    apply (hp i w).trans
    apply mul_le_mul_of_nonneg_right _ (pos w)
    exact mul_le_mul (Finset.single_le_sum (fun j _=>hC j) (Finset.mem_univ i))
      (pow_le_pow_right₀ (large w) (Finset.single_le_sum (fun j _=>Nat.zero_le (k j)) (Finset.mem_univ i)))
      (pow_nonneg ((zero_le_one (α:=ℝ)).trans (large w)) _)
      (Finset.sum_nonneg (fun j _=>hC j))
  calc
    ‖∑ i,c w i*F i w‖ ≤ ∑ i,‖c w i*F i w‖ := norm_sum_le _ _
    _ ≤ ∑ i,‖c w i‖*((∑ j,C j)*(mod w)^(∑ j,k j)*rate w) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (payment i) (norm_nonneg _)
    _ = (∑ i,‖c w i‖)*((∑ j,C j)*(mod w)^(∑ j,k j)*rate w) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (cash w)
      (mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun j _=>hC j)) (pow_nonneg (by linarith [large w]) _)) (pos w))

theorem joined (u v a b x:ℝ)(q:ℕ)(trueRow:a-(if 2≤q then b else 0)=x) :
    ‖(u-(if 2≤q then v else 0))-x‖ ≤ ‖a-u‖+‖b-v‖ := by
  subst x
  by_cases h:2≤q
  · simp only [if_pos h]
    rw [show u-v-(a-b)=(u-a)+(b-v) from by ring]
    exact (norm_add_le _ _).trans_eq (by rw [norm_sub_rev u a])
  · simp only [if_neg h,sub_zero,norm_sub_rev u a]
    exact le_add_of_nonneg_right (norm_nonneg _)

end YM.Integration.WilsonIndependentWardFiniteBudget
