import YM.RG08.Supplies.Caps
import YM.RG08.Yamen.Penny

/-!
# Existing post-length payment for the original native Gaussian kernels

The positive PlanCurve is chosen from G, the raw kernel, and the retained
MapPrices before L. The actual post-L Yamen payment bounds planSupply and
the predictor key by log(hatBeta). These bounds keep the same Horizon and
the complete native covariance and predictor, including every-period
Tagged matrix identities. No new payment or different Run is selected.

On the common construction, use Realized.supplies.housed and
Realized.payment. Identification with an arbitrary Bulk.Chain's actual
inverse Hessian, finite Wick extraction, and NumericSchedule admission
remain separate applications.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativePaidKernelCosts
open Lattice Laurent RG Precision Stationary Bloch
open RG08 RG08.Supplies RG08.Rows RG08.Cell RG08.Line
open scoped Classical

variable {G : Gauge} {a : Levels G} {H : Horizon a}
  {P X : MapPrices} {Z : ChartRatio G}

/-- All three costs come from the same already-purchased post-L stamp. -/
theorem paid_costs (hpaid : Yamen.Payment G P X Z a) (i : ℕ) :
    1 ≤ Real.log (a.clock.hatBeta i) ∧
    planSupply G a.clock.kernel P (a.clock.J (i + 1)) (a.S.block i) ≤
      Real.log (a.clock.hatBeta i) ∧
    Cell.key G (stone a i) a.clock.kernel ≤
      Real.log (a.clock.hatBeta i) ∧
    Cell.allowance G (stone a i)
        (planSupply G a.clock.kernel P (a.clock.J (i + 1)) (a.S.block i)) ≤
      Real.log (a.clock.hatBeta i) := by
  have hs := Yamen.stamped G P X a.clock.kernel Z (stone a i)
  have hp := Yamen.hatch hpaid i
  exact ⟨hs.pos.trans hp, hs.plant.trans hp,
    hs.key.trans hp, hs.allowance.trans hp⟩

/-- Full covariance with its original finite matrices, at the pre-L width. -/
theorem warm_paid (hH : H.Suffices P)
    (hpaid : Yamen.Payment G P X Z a) (N i : ℕ) (hi : i < N) :
    Warm G a.clock.kernel (stone a i) (H.H N (i + 1))
      (PlanCurve G a.clock.kernel P (a.clock.J (i + 1)))
      (Real.log (a.clock.hatBeta i)) := by
  have hw : Warm G a.clock.kernel (stone a i) (H.H N (i + 1))
      (PlanCurve G a.clock.kernel P (a.clock.J (i + 1)))
      (planSupply G a.clock.kernel P (a.clock.J (i + 1)) (a.S.block i)) :=
    (planSupply_spec G a.clock.kernel P _).2 _
      (a.blocks i 0).branches rfl _
      (hH.rows N (i + 1) hi).2.1 _ _
      (fun n => hH.all N (i + 1) hi n)
  exact ⟨hw.bill.mono le_rfl (paid_costs hpaid i).2.1, hw.invert⟩

/-- Full predictor price, with every-period matrix equality unchanged. -/
theorem predictor_paid (hH : H.Suffices P)
    (hpaid : Yamen.Payment G P X Z a) (N i : ℕ) (hi : i < N) :
    Tagged (PlanCurve G a.clock.kernel P (a.clock.J (i + 1)))
      ((Real.log (a.clock.hatBeta i)) ^ 2)
      (Cell.predictor (stone a i) a.clock.kernel G (H.H N (i + 1)))
      (Cell.predictorFinite (stone a i) a.clock.kernel G (H.H N (i + 1))) := by
  have hw := warm_paid hH hpaid N i hi
  have hwidth := plan_hr G a.clock.kernel P (a.clock.J (i + 1))
  have hcost := paid_costs hpaid i
  have hlog : 0 ≤ Real.log (a.clock.hatBeta i) :=
    zero_le_one.trans hcost.1
  have hp := Cell.predictor_price (stone a i) a.clock.kernel G
    (H.H N (i + 1)) hw hwidth.1.le hwidth.2.1
  apply hp.mono le_rfl
  simpa only [pow_two] using
    (mul_le_mul_of_nonneg_left hcost.2.2.1 hlog)

end YM.Integration.NativePaidKernelCosts
end
