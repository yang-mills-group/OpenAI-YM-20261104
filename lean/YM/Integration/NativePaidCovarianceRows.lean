import YM.Integration.NativePaidRootFieldColumns
import YM.RG08.Cell.Release

/-!
Full fine-coordinate covariance row sums, on the same original Run.
The native spread carries laneTax = L^4 * exp(8). The same post-L stamp
pays L and the packed covariance, yielding exp(8) * log(hatBeta)^5.
The explicit physical axis/color count is retained after periodization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativePaidCovarianceRows
open Lattice Laurent RG Precision Stationary Bloch
open RG08 RG08.Supplies RG08.Rows RG08.Cell RG08.Line
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G : Gauge} {a : Levels G} {H : Horizon a}
  {P X : MapPrices} {Z : ChartRatio G}

/-- Both original cover bills survive the complete L^4 spread tax. -/
theorem market_paid (hH : H.Suffices P)
    (hpaid : Yamen.Payment G P X Z a) (N i : ℕ) (hi : i < N) :
    Cell.marketBill (a.S.block i)
      (Cell.sliced (stone a i) a.clock.kernel G (H.H N (i + 1)))
      (PlanCurve G a.clock.kernel P (a.clock.J (i + 1)))
      (Real.exp 8 * (Real.log (a.clock.hatBeta i)) ^ 5) := by
  have hwidth := plan_hr G a.clock.kernel P (a.clock.J (i + 1))
  have hlog : 0 ≤ Real.log (a.clock.hatBeta i) :=
    zero_le_one.trans (NativePaidKernelCosts.paid_costs hpaid i).1
  have hw := NativePaidKernelCosts.warm_paid hH hpaid N i hi
  have hm := Cell.market_release hw.bill.toPriced hwidth.1.le hwidth.2.1
  have hL := NativePaidRootFieldColumns.length_paid hpaid i
  have hL4 : (((a.S.block i).val : ℝ) ^ 4) ≤
      (Real.log (a.clock.hatBeta i)) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hL 4
  have hcost : Cell.laneTax (a.S.block i) * Real.log (a.clock.hatBeta i) ≤
      Real.exp 8 * (Real.log (a.clock.hatBeta i)) ^ 5 := by
    unfold Cell.laneTax
    calc
      _ ≤ (((Real.log (a.clock.hatBeta i)) ^ 4) * Real.exp 8) *
          Real.log (a.clock.hatBeta i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hL4 (Real.exp_pos 8).le) hlog
      _ = _ := by ring
  exact ⟨fun x j => (hm.1 x j).trans (ENNReal.ofReal_le_ofReal hcost),
    fun j x => (hm.2.1 j x).trans (ENNReal.ofReal_le_ofReal hcost), hm.2.2⟩

/-- The full finite row, summed over every original fine coordinate.
The bound does not substitute the smaller packed-cell Warm price. -/
theorem covariance_row (R : Run G)
    (hAttached : ActualRunNativeComponentRecipe.Attached R)
    (N period i : ℕ) (hi : i < N)
    (x : Lines G (R.family.path.levels.S.side (i + 1) period) 1) :
    (∑ y : Lines G (R.family.path.levels.S.side (i + 1) period) 1,
      |NativeLine (R.family.path.levels.clock.op i period) G
        (R.alloy.B.M.H N (i + 1)) x y|) ≤
      (Fintype.card (Loc G 1) : ℝ) *
        (Real.exp 8 * (Real.log (R.family.path.levels.clock.hatBeta i)) ^ 5) := by
  obtain ⟨s, T, C, n, -, -, -, hquote, -, -, -, hReal⟩ := hAttached
  have hpaid : Yamen.Payment G R.metals.K C.secondary
      (Next.Foundations.chart G) R.family.path.levels := by
    rw [hquote]
    exact hReal.payment
  have hm := market_paid R.alloy.B.plan hpaid N i hi
  have hwidth := plan_hr G R.family.path.levels.clock.kernel R.metals.K
    (R.family.path.levels.clock.J (i + 1))
  have hs : 0 ≤
      PlanCurve G R.family.path.levels.clock.kernel R.metals.K
        (R.family.path.levels.clock.J (i + 1)) /
        (R.family.path.levels.S.block i).val :=
    div_nonneg hwidth.1.le (Nat.cast_nonneg _)
  have hprice : 0 ≤ Real.exp 8 *
      (Real.log (R.family.path.levels.clock.hatBeta i)) ^ 5 :=
    mul_nonneg (Real.exp_pos 8).le
      (pow_nonneg (zero_le_one.trans
        (NativePaidKernelCosts.paid_costs hpaid i).1) 5)
  exact NativeFiniteMatrixCosts.row_sum_le
    (ActualNativeKernelDictionary.actual_matrices R N period i hi).1
    (hm.1.mono hs) hprice x

end YM.Integration.NativePaidCovarianceRows
end
