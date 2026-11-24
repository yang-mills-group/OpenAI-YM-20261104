import YM.Integration.NativeFiniteMatrixCosts
import YM.Integration.NativePaidKernelCosts
import YM.Integration.ActualNativeKernelDictionary
import YM.Integration.ActualRunNativeComponentRecipe

/-!
The original post-L stamp pays the complete finite-period RootField column.
The cover column carries L^4 * exp(4*sigma); the same stamp pays L by log,
while the packed predictor costs log^2. The resulting bound is exp(4)*log^6,
times the explicit output axis/color count. No rectangular column estimate
is inferred from a row estimate, and no block multiplicity is discarded.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativePaidRootFieldColumns
open Lattice Laurent RG Precision Stationary Bloch
open RG08 RG08.Supplies RG08.Rows RG08.Cell RG08.Line
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G : Gauge} {a : Levels G} {H : Horizon a}
  {P X : MapPrices} {Z : ChartRatio G}

/-- This is the length field of the same stamp used for the kernel bill. -/
theorem length_paid (hpaid : Yamen.Payment G P X Z a) (i : ℕ) :
    ((a.S.block i).val : ℝ) ≤ Real.log (a.clock.hatBeta i) :=
  (Yamen.stamped G P X a.clock.kernel Z (stone a i)).length.trans
    (Yamen.hatch hpaid i)

/-- The full cover column and row retain the native block-volume factor,
paid by the actual length receipt at the same stage. -/
theorem outward_paid (hH : H.Suffices P)
    (hpaid : Yamen.Payment G P X Z a) (N i : ℕ) (hi : i < N) :
    Cell.outward
      (Cell.plotted (stone a i) a.clock.kernel G (H.H N (i + 1)))
      (a.S.block i)
      (PlanCurve G a.clock.kernel P (a.clock.J (i + 1)))
      (Real.exp 4 * (Real.log (a.clock.hatBeta i)) ^ 6) := by
  have hwidth := plan_hr G a.clock.kernel P (a.clock.J (i + 1))
  have hlog : 0 ≤ Real.log (a.clock.hatBeta i) :=
    zero_le_one.trans (NativePaidKernelCosts.paid_costs hpaid i).1
  have hout := Cell.out_bill hwidth.1.le
    (NativePaidKernelCosts.predictor_paid hH hpaid N i hi).toPriced
  have hL := length_paid hpaid i
  have hL4 : (((a.S.block i).val : ℝ) ^ 4) ≤
      (Real.log (a.clock.hatBeta i)) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hL 4
  have he : Real.exp
      (4 * PlanCurve G a.clock.kernel P (a.clock.J (i + 1))) ≤
      Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    have hσ : PlanCurve G a.clock.kernel P (a.clock.J (i + 1)) ≤ 1 := hwidth.2.1
    linarith only [hσ]
  have hbase :=
    mul_le_mul hL4 he (Real.exp_pos _).le (pow_nonneg hlog 4)
  have hcost :
      ((((a.S.block i).val : ℝ) ^ 4) *
        Real.exp (4 * PlanCurve G a.clock.kernel P (a.clock.J (i + 1)))) *
          ((Real.log (a.clock.hatBeta i)) ^ 2) ≤
        Real.exp 4 * (Real.log (a.clock.hatBeta i)) ^ 6 := by
    calc
      _ ≤ (((Real.log (a.clock.hatBeta i)) ^ 4) * Real.exp 4) *
          ((Real.log (a.clock.hatBeta i)) ^ 2) :=
        mul_le_mul_of_nonneg_right hbase (sq_nonneg _)
      _ = _ := by ring
  exact
    { row := fun x j => (hout.row x j).trans (ENNReal.ofReal_le_ofReal hcost)
      col := fun j x => (hout.col j x).trans (ENNReal.ofReal_le_ofReal hcost)
      marked := hout.marked }

/-- Every column is the complete original finite RootField column. The
existing component attachment supplies payment on this same Run. -/
theorem root_column (R : Run G)
    (hAttached : ActualRunNativeComponentRecipe.Attached R)
    (N period i : ℕ) (hi : i < N)
    (y : Lines G (R.family.path.levels.S.side i period) 1) :
    (∑ x : Lines G (R.family.path.levels.S.side (i + 1) period) 1,
      |Cell.RootField R.family.path.levels.clock.kernel G
        (R.family.path.levels.clock.op i period)
        (R.alloy.B.M.H N (i + 1)) x y|) ≤
      (Fintype.card (Loc G 1) : ℝ) *
        (Real.exp 4 * (Real.log (R.family.path.levels.clock.hatBeta i)) ^ 6) := by
  obtain ⟨s, T, C, n, -, -, -, hquote, -, -, -, hReal⟩ := hAttached
  have hpaid : Yamen.Payment G R.metals.K C.secondary
      (Next.Foundations.chart G) R.family.path.levels := by
    rw [hquote]
    exact hReal.payment
  have hout := outward_paid R.alloy.B.plan hpaid N i hi
  have hwidth := plan_hr G R.family.path.levels.clock.kernel R.metals.K
    (R.family.path.levels.clock.J (i + 1))
  have hprice : 0 ≤ Real.exp 4 *
      (Real.log (R.family.path.levels.clock.hatBeta i)) ^ 6 :=
    mul_nonneg (Real.exp_pos 4).le
      (pow_nonneg (zero_le_one.trans
        (NativePaidKernelCosts.paid_costs hpaid i).1) 6)
  exact NativeFiniteMatrixCosts.column_sum_le
    (R.family.path.levels.clock.op i period).sizes hout.marked
    (ActualNativeKernelDictionary.actual_matrices R N period i hi).2
    (hout.col.mono hwidth.1.le) hprice y

end YM.Integration.NativePaidRootFieldColumns
end
