import YM.Integration.LocalComparisonFullDensity
import YM.Integration.LocalComparisonReclosureReadout

/-!
The complete raw residual bound applied to the exact external qlocal receipt.
The true carrier, reserved support norm and all independent tests are retained.
The remaining flagged exponential background must still be integrated under
the actual normalized law; this theorem does not assume that estimate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker
open RG3.Script.Picnic Comparison.RG02 SectorNext.Vacuum
open scoped Classical

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

/-- Concrete whole-density consequence of the residual norm, including its
forced and mixed terms. The scalar late-stage smallness condition is exposed
for the existing clock supplier to discharge. -/
theorem MarkedReclosure.residual_density_error_price
    (hC : C.Makes)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
          forcedOrder) ≤ 1)
    (x : IndependentTests D) (U : Config G (C.side datum.level datum.period)) :
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)
    let e := markedRate order delta constant geometry inherited calibration g
    Poly.price (fun v => w v / kernelCosts v)
      ((H.residual.leaf (testInclusion D x)).density U -
        (H.carrier.rep.eval U : ℂ) • (1 : Poly R)) ≤
      H.carrier.rep.eval U * (Real.exp (Fintype.card V * e) - 1) +
      (Real.exp (H.carrier.rep.exponent U) * Real.exp (Fintype.card V * e)) *
        (if flags H.carrier.rep.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (forcedDivisor C datum.level * g ^ forcedOrder)) *
            Real.exp (-flagRate p * (flags H.carrier.rep.p.threshold U).card)) := by
  have hP : H.carrier.rep.activities.Valid H.carrier.rep.p
      (C.path.levels.clock.allowance datum.level)
      (C.path.levels.clock.forcedAllowance datum.level) := by
    rw [H.carrier.point]
    exact H.total
  exact actual_full_density_error_price hC datum.below.le H.carrier
    H.residual_price H.output_kernel_positive
    (H.norm_threshold.trans (congrArg BudgetPoint.threshold H.carrier.point).symm)
    hP H.vacuum_reserve hSmall x U

end YM.Integration.LocalComparison
