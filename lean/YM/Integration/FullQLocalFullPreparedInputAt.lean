import YM.Integration.FullQLocalFullPreparedInput
import YM.Integration.LocalComparisonFullPreparationAt

/-!
Full-channel physical input paid at the requested norm. The old native-norm
input is preserved in its own module. A native-to-requested conversion must
supply the genuine budget restriction on the unchanged residual.

The produced-output constructor below retains the actual full output and
its original residual rows. It consumes their actual requested-norm bill
and the exact retuned physical read, with no channel erased.
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

structure FullPreparedInputAt (F : AnalyticInput J A datum) (eta_w : ℝ) where
  carrier : PhysicalCarrier C datum.cutoff datum.period (datum.level + 1)
  wellFormed : WellFormed (A.inputNorm datum.level) carrier.rep
  inherited : ℝ
  inherited_nonnegative : 0 ≤ inherited
  inherited_bound : inherited ≤ J.inheritedConstant *
    Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ^
      ((J.order : ℝ) + 1 - J.eta)
  error : Payload G (C.side (datum.level + 1) datum.period)
  error_paid : error.Invoice (A.inputNorm datum.level) inherited
  calibration : CalibrationPresentation carrier.rep (A.inputNorm datum.level) eta_w
  exponent U : carrier.rep.exponent U = carrier.rep.scalar -
    ((C.path.rep datum.cutoff datum.period (datum.level + 1)).path.inChannels
      carrier.rep.clip carrier.rep.p
      (C.path.β datum.cutoff datum.period (datum.level + 1)) U +
      Render.renders (Render.prefactor
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)))
        carrier.rep.p U F.layers) -
    error.amount (A.inputNorm datum.level) U - calibration.amount U
  input : Taste (TestSpace J.tests) F.fineRoots carrier.rep R
  multilinear : Multilinear J.tests input
  input_retains : FunctionalRetains input F.inputAddresses
  regularPrice : ℝ
  forcedPrice : ℝ
  forced_bound : forcedPrice ≤ J.forcedConstant
  prepared : LocalComparison.Global.PreparedWithRemainderAt datum.cutoff datum.period (datum.level + 1)
    (A.inputNorm datum.level)
    (Handoff.legacyCarrier carrier) F.fineRoots input F.colors F.packets F.inputRadii
    (envelopeProduct F.kernelCosts) regularPrice forcedPrice

/-- Changing the paying norm requires its actual full budget on the same
remainder. The physical input and all vacuum data are copied literally. -/
def FullPreparedInput.withRequestedBudget {F : AnalyticInput J A datum} {eta_w : ℝ}
    (I : FullPreparedInput F eta_w)
    (hBudget : RelativeBudget (A.inputNorm datum.level)
      (pullback (testInclusion J.tests) I.prepared.remainder) F.inputRadii
      (forcedDivisor C (datum.level + 1)) (envelopeProduct F.kernelCosts)
      I.regularPrice I.forcedPrice) : FullPreparedInputAt F eta_w where
  carrier := I.carrier
  wellFormed := I.wellFormed
  inherited := I.inherited
  inherited_nonnegative := I.inherited_nonnegative
  inherited_bound := I.inherited_bound
  error := I.error
  error_paid := I.error_paid
  calibration := I.calibration
  exponent := I.exponent
  input := I.input
  multilinear := I.multilinear
  input_retains := I.input_retains
  regularPrice := I.regularPrice
  forcedPrice := I.forcedPrice
  forced_bound := I.forced_bound
  prepared := {
    convention := I.prepared.convention
    remainder := I.prepared.remainder
    full := I.prepared.full
    remainder_price := hBudget
  }

/-- The physical WellFormed receipt supplies the exact threshold equality;
the K bound and marked bill use that identical requested norm. -/
theorem FullPreparedInputAt.normalized_defect_price
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    (I : FullPreparedInputAt F eta_w) {vacuum : ℝ}
    (hReserve : I.carrier.rep.activities.KBound (A.inputNorm datum.level) vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) *
      (forcedDivisor C (datum.level + 1) * I.forcedPrice) ≤ 1)
    (x : IndependentTests J.tests)
    (U : Config G (C.side (datum.level + 1) datum.period))
    (hVacuum : 0 < I.carrier.rep.eval U) :
    Poly.price (fun v => F.inputRadii v / F.kernelCosts v)
      ((I.carrier.rep.eval U : ℂ)⁻¹ •
        (I.input.leaf (testInclusion J.tests x)).density U -
        Poly.pass (F.packets.read (testInclusion J.tests x)
          (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
            (datum.level + 1)) U)) ≤
      Poly.price (fun v => F.inputRadii v / F.kernelCosts v)
        (Poly.pass (F.packets.read (testInclusion J.tests x)
          (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
            (datum.level + 1)) U)) *
        retainedErrorBoundAt (V := V) (A.inputNorm datum.level)
          (Handoff.legacyCarrier I.carrier) I.regularPrice I.forcedPrice U := by
  exact I.prepared.normalized_defect_price F.kernel_positive
    I.wellFormed.threshold hReserve hSmall x U hVacuum

/-- The actual produced output, including its whole rough residual, has the
next preparation factorization once the retuned packet has the exact read.
Its original row budget is used directly at q; no density-to-row transfer
or replacement by formalAligned occurs. -/
def prepareProduced {D : V → ComparisonDensity.Address.Orbit}
    {N period m : ℕ} {fine : PhysicalCarrier C N period (m + 1)}
    {fineRoots : V → Site (C.side (m + 1) period)}
    {coarseRoots : V → Site (C.side m period)}
    {input : Taste (TestSpace D) fineRoots fine.rep R}
    (O : ProducedOutput D fine fineRoots coarseRoots input)
    (q : BudgetPoint)
    (colors : TestSpace D → Bulk.Colors R G (C.side m period))
    (packets : MarkedPackets D G (C.side m period) R)
    (w cost : V → ℝ) (regularPrice forcedPrice : ℝ)
    (hColors : InputColors colors packets)
    (hRead : ∀ x U,
      packets.read x (Pert.Asymptotics.regulatorRun C N period m) U =
        O.model.read x (Pert.Asymptotics.regulatorRun C N period (m + 1)) U)
    (hBudget : RelativeBudget q
      (pullback (testInclusion D) O.residual) w (forcedDivisor C m)
      (envelopeProduct cost) regularPrice forcedPrice) :
    PreparedWithRemainderAt N period m q (Handoff.legacyCarrier O.carrier)
      coarseRoots O.output colors packets w (envelopeProduct cost)
      regularPrice forcedPrice where
  convention := hColors
  remainder := O.residual
  full := by
    intro x U
    rw [hRead]
    exact O.full x U
  remainder_price := hBudget

end YM.Integration.FullQLocal.RenderedStep.Numeric
end
