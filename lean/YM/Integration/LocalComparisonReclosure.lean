import YM.Integration.LocalComparisonPackets
import YM.Integration.LocalComparisonEnvelope
import YM.Integration.LocalComparisonInput
import YM.Integration.LocalComparisonVacuum
import YM.Pert.Asymptotics.RawAxis

/-! Concrete marked output portion of the external local comparison.

This is a receipt to be constructed by the missing supplier, not a theorem
asserting its existence. The input, literal formal packet model, represented
residual, full output and next-use budget all share the specified physical
step. Vacuum approximation and uniform tail quantifiers are separate portions
of the complete external deliverable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic
open Comparison.RG02
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {C : Family G} {D : V → ComparisonDensity.Address.Orbit}

/-- The regular marked rate. -/
def markedRate (order : ℕ) (delta constant geometry inherited calibration coupling : ℝ) : ℝ :=
  constant * coupling ^ ((order : ℝ) + 1 - delta) +
    geometry * (inherited + calibration)

/-- A complete marked comparison on one fixed step. The model is the literal
unmasked curvature completion `model.read`; the residual still carries all
forced alternatives on the actual vacuum, so the equality is of the whole
unnormalized polynomial. No raw subtraction of differently labelled
representations appears in this receipt.

`nextRegular` and `nextForced` name the separately announced next-use source
budgets. This record does not choose them or assert that arbitrary requested
budgets are available. Their original propagation rules belong to the
repeated-use portion of the external deliverable.

The displayed carrier beta may differ from the physical kernel beta. Its
full native validity and exact vacuum are retained; the existing rigidity
supplier gives the eventual beta-gap bound separately. This record does not
replace that gap by an equality or claim ordinary next-step admission from
an equality of densities alone.
-/
structure MarkedReclosure (Y : Bulk.Chain C.path) (datum : LocalFormal.Datum C R)
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
  output_addresses : Retains output addresses
  residual_addresses : Retains residual addresses
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

end YM.Integration.LocalComparison
