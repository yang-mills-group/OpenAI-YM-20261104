import YM.Integration.FullQLocalNumericStepData

/-!
The complete preserved selected-output records on NumericSchedule.

Every physical formula and retained input remains unchanged. This vocabulary
states no selected output or full manuscript grant. The actual component
window, weak-domain construction and repeated input remain application duties.
The previous selected-output records remain in their original namespace.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}
    {J : Request V} {A : NumericSchedule C J} {datum : LocalFormal.Datum C R}
    {caps : Handoff.OutputCapacities}

/-- Explicit strong inlet only. This is not a renamed weak-stage predicate. -/
structure StrongInput {F : AnalyticInput J A datum} {eta_w : ℝ}
    (I : PreparedInput F eta_w) : Prop where
  original : I.carrier.rep.activities.KBound
    (C.path.levels.budget (datum.level + 1))
    (C.path.levels.clock.forcedAllowance (datum.level + 1))
  reserved : I.carrier.rep.activities.KBound (A.inputNorm datum.level)
    (C.path.levels.clock.forcedAllowance (datum.level + 1))

/-- Primary data is one complete functional on the already chosen output. -/
structure ChosenPrimary {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : PreparedInput F eta_w}
    (O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input) where
  coefficient : (v : V) → TestSpace J.tests →
    Source.Coefficient (C.labels.level (J.outputWeight v))
      (C.side datum.level datum.period)
  support v x y : (coefficient v x).support = (coefficient v y).support
  format v x : (coefficient v x).Format (F.coarseRoots v) C.params O.carrier.rep
  remainder v x : ∃ k r, (coefficient v x).remBound (F.coarseRoots v) O.carrier.rep k r
  singleton v x U : (coefficient v x).density (F.coarseRoots v)
    (C.localSection (J.outputWeight v)) O.carrier.rep U =
      ((O.output.leaf x).density U).part (R.fire v)

def ChosenPrimary.Bound {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : PreparedInput F eta_w}
    {O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input}
    (P : ChosenPrimary O) (price : ℝ) : Prop :=
  ∀ (v : V) (x : IndependentTests J.tests),
    (F.outputRadii v / F.kernelCosts v) *
      (C.labels.level (J.outputWeight v)).coeffSize
        (Trace.Physical.Germ.projection (C.labels.level (J.outputWeight v)) C.params
          O.carrier.rep.p.threshold (F.coarseRoots v)
          (P.coefficient v (testInclusion J.tests x)) -
        Trace.Physical.Germ.vector (C.labels.level (J.outputWeight v)) C.params
          O.carrier.rep.p.threshold (F.coarseRoots v)
          (fun U => (O.model.read (testInclusion J.tests x)
            (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
              (datum.level + 1)) U).part (R.fire v))) ≤ price

/-- The native pre-reset source and its bound use the same produced carrier.
No older-error kinetic correction is extracted here: alpha is literally zero,
and every such contribution remains inside the bounded raw source. A later
scalar/coupling reset and its exact costs belong to the downstream application. -/
structure ChosenVacuum {Y : Bulk.Chain C.path} (K : NumericPrices A)
    {F : AnalyticInput J A datum} {eta_w : ℝ} (I : PreparedInput F eta_w)
    (M : AnalyticOutput caps Y K F)
    (O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input) where
  listing : AnalyticBridge.VerifiedReset.Collection.Listing G
    (C.side datum.level datum.period)
  source : AnalyticBridge.VerifiedReset.Collection.Source G
    (C.side datum.level datum.period)
  scalar : ℝ
  estimate : AnalyticBridge.VerifiedReset.Collection.Local listing
    (A.outputNorm datum.level) source
    (vacuumRate J.order K.vacuumConstant (C.S.block datum.level).val
      (K.vanishing datum.level) (K.geometry datum.level) I.inherited eta_w
      (Currency.g C datum.cutoff datum.period (datum.level + 1)))
    (C.path.levels.clock.forcedAllowance datum.level)
  representation : O.carrier.rep =
    PreReset.append (M.plan.layers datum.level)
      (C.path.rep datum.cutoff datum.period datum.level).path
      (C.path.levels.params datum.level).clip (C.path.levels.budget datum.level)
      listing source (M.plan.predict datum.level) scalar 0
      (Render.prefactor (Currency.gain (M.plan.predict datum.level)))

/-- One complete joint witness. The chosen model is fixed before I; the
vacuum, formal companion, aligned residual and primary precede delta and A. -/
structure Chosen {Y : Bulk.Chain C.path} (K : NumericPrices A)
    {F : AnalyticInput J A datum} {eta_w : ℝ} (I : PreparedInput F eta_w)
    (M : AnalyticOutput caps Y K F) where
  output : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input
  same_model : output.model = M.model
  wellFormed : WellFormed (A.outputNorm datum.level) output.carrier.rep
  actual_forced : output.carrier.rep.activities.KBound
    (C.path.levels.budget datum.level) (C.path.levels.clock.forcedAllowance datum.level)
  fixed_forced : output.carrier.rep.activities.KBound
    (A.outputNorm datum.level) (C.path.levels.clock.forcedAllowance datum.level)
  output_active x : (output.output.leaf x).Active
  formal_active x : (output.formalAligned.leaf x).Active
  output_multilinear : Multilinear J.tests output.output
  formal_multilinear : Multilinear J.tests output.formalAligned
  residual_multilinear : Multilinear J.tests output.residual
  output_retains : FunctionalRetains output.output F.outputAddresses
  formal_retains : FunctionalRetains output.formalAligned F.outputAddresses
  residual_retains : FunctionalRetains output.residual F.outputAddresses
  aligned : QlocalMarkedPrimaryProposal.AlignedRegularRows
    output.output output.formalAligned output.residual
  vacuum : ChosenVacuum K I M output
  primary : ChosenPrimary output

/-- Only estimates/majorants vary with the later requests. The exact max norm
and the native factorial currency are stated separately on the same residual;
no definitional equality between those norms is asserted. -/
structure Bounds {Y : Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ} {I : PreparedInput F eta_w}
    {M : AnalyticOutput caps Y K F} (S : Chosen K I M) (delta : ℝ) (forcedOrder : ℕ) where
  connected : QlocalMarkedPrimaryProposal.IndependentConnectedClause J.tests
    (A.outputNorm datum.level) S.output.residual F.outputRadii
    (envelopeProduct F.kernelCosts)
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited eta_w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
  residual_price : RelativeBudget (A.outputNorm datum.level)
    (pullback (testInclusion J.tests) S.output.residual) F.outputRadii
    (forcedDivisor C datum.level) (envelopeProduct F.kernelCosts)
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited eta_w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)
  primary : S.primary.Bound
    (markedRate J.order delta (K.markedConstant delta) (K.geometry datum.level)
      I.inherited eta_w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
  forced : ForcedBudget (A.outputNorm datum.level)
    (priceNormalized (envelopeProduct F.kernelCosts)
      (pullback (testInclusion J.tests) S.output.output)) F.outputRadii
    (forcedDivisor C datum.level)
    ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
      forcedOrder)

end YM.Integration.FullQLocal.RenderedStep.Numeric
end
