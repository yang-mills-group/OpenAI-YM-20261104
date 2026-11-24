import YM.Integration.ActualBetaFirstOrderCost
import YM.Integration.ActualBetaUnitFirstOrder

/-! The exact finite-copy bill has a first-order bound at every truncation
order, including zero. At zero the full correcting copy is retained rather
than discarded. All constants are chosen from the original exponent cap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualBetaRemainder

open ActualBetaUnitFirstOrder

/-- The zero-order expansion consists of precisely the original correcting
factor. This identity needs neither smallness nor a nonzero coupling. -/
theorem retuning_zero (e : ℤ) (delta g : ℝ) :
    coefficientBill e delta g 0 +
      |correctionCoefficient e delta g 0| * |g| ^ (2 * 0) =
        |unit delta g ^ e| := by
  simp [coefficientBill, correctionCoefficient, truncated_sum]

/-- A single cap-only constant pays the complete bill for every n:Nat.
The original physical nonzero-coupling and half-radius premises are retained. -/
theorem full_retuning_all_orders (cap : ℕ) :
    ∃ D > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta g : ℝ,
      g ≠ 0 → |delta * g ^ 2| ≤ 1 / 2 → ∀ n : ℕ,
        coefficientBill e delta g n +
          |correctionCoefficient e delta g n| * |g| ^ (2 * n) ≤
            1 + D * |delta * g ^ 2| := by
  obtain ⟨A, hA, hpositive⟩ := full_retuning_first_order cap
  obtain ⟨B, hB, hunit⟩ := unit_and_inverse_bounds cap
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro e he delta g hg hsmall n
  cases n with
  | zero =>
      rw [retuning_zero]
      refine (hunit e he delta g hsmall).1.trans ?_
      nlinarith [mul_nonneg hA.le (abs_nonneg (delta * g ^ 2))]
  | succ n =>
      refine (hpositive e he delta g hg hsmall (n + 1) (by omega)).trans ?_
      nlinarith [mul_nonneg hB.le (abs_nonneg (delta * g ^ 2))]

end YM.Integration.ActualBetaRemainder
end
