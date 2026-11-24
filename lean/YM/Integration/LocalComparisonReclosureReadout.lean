import YM.Integration.LocalComparisonPhysicalReadout
import YM.Integration.LocalComparisonReclosure

/-!
Concrete downstream use of the external marked-reclosure receipt.
Its literal residual and next-step output are kept on the same carrier.
The conclusions below discharge their regular/caption scalar norm conversion;
the forced residual and the existence of the external receipt remain separate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker
open RG3.Script.Picnic Comparison.RG02 UniformPolynomialComparison
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {C : Family G} {D : V → ComparisonDensity.Address.Orbit}
    {Y : Bulk.Chain C.path} {datum : LocalFormal.Datum C R}
    {inputColors : TestSpace D → Bulk.Colors R G (C.side (datum.level + 1) datum.period)}
    {inputCarrier : Carrier C datum.cutoff datum.period (datum.level + 1)}
    {fineRoots : V → Site (C.side (datum.level + 1) datum.period)}
    {coarseRoots : V → Site (C.side datum.level datum.period)}
    {input : Taste (TestSpace D) fineRoots inputCarrier.rep R}
    {inputPackets : MarkedPackets D G (C.side (datum.level + 1) datum.period) R}
    {inputRadii inputKernelCosts : V → ℝ} {inputForcedPrice : ℝ}
    {model : MarkedPackets D G (C.side datum.level datum.period) R}
    {order forcedOrder : ℕ} {p : BudgetPoint} {w kernelCosts : V → ℝ}
    {delta constant geometry inherited calibration nextRegular nextForced : ℝ}
    {addresses : V → Support (C.side datum.level datum.period)}
    (H : MarkedReclosure Y datum inputColors inputCarrier fineRoots coarseRoots input
      inputPackets inputRadii inputKernelCosts inputForcedPrice model order forcedOrder p w
      kernelCosts delta constant geometry inherited calibration nextRegular nextForced addresses)

/-- The actual retained residual log at the displayed qlocal rate, with the
independent test supremum inside each coefficient and original kernel costs. -/
theorem MarkedReclosure.residual_log_price :
    uniformPrice (fun v => w v / kernelCosts v)
      (fun z : IndependentTests D × Config G (C.side datum.level datum.period) =>
        (H.residual.leaf (testInclusion D z.1)).log z.2) ≤
      Fintype.card V * markedRate order delta constant geometry inherited calibration
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) := by
  exact H.residual_price.physical_uniform_log_price H.output_kernel_positive
    (zeroIndependentTests D)
    (H.norm_threshold.trans (congrArg BudgetPoint.threshold H.carrier.point).symm)

/-- The nonlinear regular/caption contribution of the SAME residual.  Its
forced gas is not omitted from H.full or identified with this factor. -/
theorem MarkedReclosure.residual_log_exponential_error :
    uniformPrice (fun v => w v / kernelCosts v)
      (fun z : IndependentTests D × Config G (C.side datum.level datum.period) =>
        Poly.pass ((H.residual.leaf (testInclusion D z.1)).log z.2) - 1) ≤
      Real.exp (Fintype.card V *
        markedRate order delta constant geometry inherited calibration
          (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))) - 1 := by
  exact independent_test_log_exponential_error H.residual_price H.output_kernel_positive
    (H.norm_threshold.trans (congrArg BudgetPoint.threshold H.carrier.point).symm)

/-- The exact next-use output on the same physical carrier has its own
announced regular scalar price; no repeated admission is inferred from this. -/
theorem MarkedReclosure.next_log_price :
    uniformPrice w
      (fun z : IndependentTests D × Config G (C.side datum.level datum.period) =>
        (H.output.leaf (testInclusion D z.1)).log z.2) ≤
      Fintype.card V * nextRegular := by
  exact H.next_price.uniform_log_price (zeroIndependentTests D)
    (congrArg BudgetPoint.threshold H.carrier.point).symm

end YM.Integration.LocalComparison
