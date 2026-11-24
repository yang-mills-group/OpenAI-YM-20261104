import YM.Integration.LocalComparisonFunctionalRetains
import YM.Integration.LocalComparisonReclosureReadout
import YM.Integration.LocalComparisonReclosureFullDensity

/-!
# Next-price consumers with locality of complete nonzero functionals

This internal receipt keeps the original prepared analytic input, physical
carrier, exact polynomial, full residual and next-use price. Its locality
condition permits identically zero padded rows in the unchanged native Active
representation. No marked row, vacuum support, flag or value is rebooked.

The four concrete consumer proofs below use the original FullBudget and
RelativeBudget directly. They prove the same regular, next-price and full
regular/forced/mixed density bounds; unconditional support retention was not
used in those analytic proofs. Supplying the next-use price and the original
preparation remains an application obligation. This is not an existence theorem
for a local comparison or a new external input.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02 UniformPolynomialComparison SectorNext.Vacuum
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {C : Family G} {D : V → ComparisonDensity.Address.Orbit}

structure FunctionalMarkedReclosure (Y : Bulk.Chain C.path) (datum : LocalFormal.Datum C R)
    (inputColors : TestSpace D → Bulk.Colors R G (C.side (datum.level + 1) datum.period))
    (inputCarrier : Carrier C datum.cutoff datum.period (datum.level + 1))
    (fineRoots : V → Site (C.side (datum.level + 1) datum.period))
    (coarseRoots : V → Site (C.side datum.level datum.period))
    (input : Taste (TestSpace D) fineRoots inputCarrier.rep R)
    (inputPackets : MarkedPackets D G (C.side (datum.level + 1) datum.period) R)
    (inputRadii inputKernelCosts : V → ℝ) (inputForcedPrice : ℝ)
    (model : MarkedPackets D G (C.side datum.level datum.period) R)
    (order forcedOrder : ℕ) (p : BudgetPoint) (w : V → ℝ)
    (kernelCosts : V → ℝ)
    (delta constant geometry inherited calibration nextRegular nextForced : ℝ)
    (addresses : V → Support (C.side datum.level datum.period)) where
  prepared_input : PreparedInput datum.cutoff datum.period (datum.level + 1)
    inputCarrier fineRoots input inputColors inputPackets
    inputRadii (envelopeProduct inputKernelCosts) inputForcedPrice
  input_kernel_positive v : 0 < inputKernelCosts v
  output_kernel_positive v : 0 < kernelCosts v
  carrier : Carrier C datum.cutoff datum.period datum.level
  total : carrier.rep.activities.Valid (C.path.levels.budget datum.level)
    (C.path.levels.clock.allowance datum.level)
    (C.path.levels.clock.forcedAllowance datum.level)
  norm_threshold : p.threshold = (C.path.levels.budget datum.level).threshold
  norm_block : p.B = (C.path.levels.budget datum.level).B
  output : Taste (TestSpace D) coarseRoots carrier.rep R
  residual : Taste (TestSpace D) coarseRoots carrier.rep R
  formal : PrescribedPackets Y datum inputColors model order
  exact : ExactStep inputCarrier carrier fineRoots coarseRoots input output
  output_multilinear : Multilinear D output
  residual_multilinear : Multilinear D residual
  output_addresses : FunctionalRetains output addresses
  residual_addresses : FunctionalRetains residual addresses
  full (x : TestSpace D) (U : Config G (C.side datum.level datum.period)) :
    (output.leaf x).density U =
      Poly.pass (model.read x
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) U) *
      (residual.leaf x).density U
  residual_price : RelativeBudget p (pullback (testInclusion D) residual) w
    (forcedDivisor C datum.level) (envelopeProduct kernelCosts)
    (markedRate order delta constant geometry inherited calibration
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^ forcedOrder)
  next_price : FullBudget (C.path.levels.budget datum.level)
    (pullback (testInclusion D) output) w (forcedDivisor C datum.level)
    nextRegular nextForced
  vacuum_reserve : carrier.rep.activities.KBound p
    (C.path.levels.clock.forcedAllowance datum.level)

section FromStrong

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

/-- The original stronger receipt embeds without changing any represented data or price. -/
def MarkedReclosure.functional :
    FunctionalMarkedReclosure Y datum inputColors inputCarrier fineRoots coarseRoots input
      inputPackets inputRadii inputKernelCosts inputForcedPrice model order forcedOrder p w
      kernelCosts delta constant geometry inherited calibration nextRegular nextForced addresses where
  prepared_input := H.prepared_input
  input_kernel_positive := H.input_kernel_positive
  output_kernel_positive := H.output_kernel_positive
  carrier := H.carrier
  total := H.total
  norm_threshold := H.norm_threshold
  norm_block := H.norm_block
  output := H.output
  residual := H.residual
  formal := H.formal
  exact := H.exact
  output_multilinear := H.output_multilinear
  residual_multilinear := H.residual_multilinear
  output_addresses := H.output_addresses.functional
  residual_addresses := H.residual_addresses.functional
  full := H.full
  residual_price := H.residual_price
  next_price := H.next_price
  vacuum_reserve := H.vacuum_reserve

end FromStrong

section Consequences

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
    (H : FunctionalMarkedReclosure Y datum inputColors inputCarrier fineRoots coarseRoots input
      inputPackets inputRadii inputKernelCosts inputForcedPrice model order forcedOrder p w
      kernelCosts delta constant geometry inherited calibration nextRegular nextForced addresses)

/-- Optional compatibility with the older stronger receipt. The two support
proofs are explicit and are not assumptions of the functional consumer path. -/
def FunctionalMarkedReclosure.toStrong
    (hOutput : Retains H.output addresses)
    (hResidual : Retains H.residual addresses) :
    MarkedReclosure Y datum inputColors inputCarrier fineRoots coarseRoots input
      inputPackets inputRadii inputKernelCosts inputForcedPrice model order forcedOrder p w
      kernelCosts delta constant geometry inherited calibration nextRegular nextForced addresses where
  prepared_input := H.prepared_input
  input_kernel_positive := H.input_kernel_positive
  output_kernel_positive := H.output_kernel_positive
  carrier := H.carrier
  total := H.total
  norm_threshold := H.norm_threshold
  norm_block := H.norm_block
  output := H.output
  residual := H.residual
  formal := H.formal
  exact := H.exact
  output_multilinear := H.output_multilinear
  residual_multilinear := H.residual_multilinear
  output_addresses := hOutput
  residual_addresses := hResidual
  full := H.full
  residual_price := H.residual_price
  next_price := H.next_price
  vacuum_reserve := H.vacuum_reserve

/-- The actual retained residual log at the displayed qlocal rate, with the
independent test supremum inside each coefficient and original kernel costs. -/
theorem FunctionalMarkedReclosure.residual_log_price :
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
theorem FunctionalMarkedReclosure.residual_log_exponential_error :
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
theorem FunctionalMarkedReclosure.next_log_price :
    uniformPrice w
      (fun z : IndependentTests D × Config G (C.side datum.level datum.period) =>
        (H.output.leaf (testInclusion D z.1)).log z.2) ≤
      Fintype.card V * nextRegular := by
  exact H.next_price.uniform_log_price (zeroIndependentTests D)
    (congrArg BudgetPoint.threshold H.carrier.point).symm

/-- Concrete whole-density consequence of the residual norm, including its
forced and mixed terms. The scalar late-stage smallness condition is exposed
for the existing clock supplier to discharge. -/
theorem FunctionalMarkedReclosure.residual_density_error_price
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

end Consequences
end YM.Integration.LocalComparison
