import YM.Integration.FullQLocalNumericStepData
import YM.Integration.LocalComparisonFullPreparation

/-!
A full-channel numerical input using the same analytic model and physical
vacuum data. The accumulated ordinary regular/unit/caption remainder price
is retained separately from the divided forced price. Initial literal
preparation embeds with ordinary price zero.

The analytic model still uses its own qelt statement. The rough remainder
uses the full majorant estimate and its actual recursive payment. This file
does not grant qelt to arbitrary rough inputs, construct a common all-test
representation from pointwise witnesses, or assert a new comparison grant.
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

structure FullPreparedInput (F : AnalyticInput J A datum) (eta_w : ℝ) where
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
  prepared : LocalComparison.Global.PreparedWithRemainder datum.cutoff datum.period (datum.level + 1)
    (Handoff.legacyCarrier carrier) F.fineRoots input F.colors F.packets F.inputRadii
    (envelopeProduct F.kernelCosts) regularPrice forcedPrice

/-- The literal zero-channel input embeds without changing its carrier,
rows, masks, full exponent, factorization, radii or either original bill. -/
def PreparedInput.withFullRemainder {F : AnalyticInput J A datum} {eta_w : ℝ}
    (I : PreparedInput F eta_w) : FullPreparedInput F eta_w where
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
  regularPrice := 0
  forcedPrice := I.forcedPrice
  forced_bound := I.forced_bound
  prepared := I.prepared.withRemainder

/-- The converse is deliberately restricted to the original literal zero
channels and zero ordinary bill. No such facts follow from a small bill. -/
def FullPreparedInput.toZeroChannels {F : AnalyticInput J A datum} {eta_w : ℝ}
    (I : FullPreparedInput F eta_w)
    (hPrice : I.regularPrice = 0)
    (hRegular : ∀ x i, I.prepared.remainder.menu.regular x i = 0)
    (hUnit : ∀ x v, I.prepared.remainder.menu.global x v = 0)
    (hCaption : ∀ x i, I.prepared.remainder.score x i = 0) :
    PreparedInput F eta_w where
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
  forcedPrice := I.forcedPrice
  forced_bound := I.forced_bound
  prepared := {
    convention := I.prepared.convention
    remainder := I.prepared.remainder
    regular_zero := hRegular
    unit_zero := hUnit
    caption_zero := hCaption
    full := I.prepared.full
    forced_price := by simpa only [hPrice] using I.prepared.remainder_price
  }

theorem PreparedInput.withFullRemainder_data {F : AnalyticInput J A datum} {eta_w : ℝ}
    (I : PreparedInput F eta_w) :
    I.withFullRemainder.carrier = I.carrier ∧
      I.withFullRemainder.input = I.input ∧
      I.withFullRemainder.prepared.remainder = I.prepared.remainder ∧
      I.withFullRemainder.regularPrice = 0 ∧
      I.withFullRemainder.forcedPrice = I.forcedPrice := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- This is the full physical normalized defect. Its ordinary term is the
actual accumulated state price, not the fresh qelt remainder price. -/
theorem FullPreparedInput.normalized_defect_price
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    (I : FullPreparedInput F eta_w) {vacuum : ℝ}
    (hReserve : I.carrier.rep.activities.KBound
      (C.path.levels.budget (datum.level + 1)) vacuum)
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
        retainedErrorBound (V := V) (Handoff.legacyCarrier I.carrier)
          I.regularPrice I.forcedPrice U := by
  exact I.prepared.normalized_defect_price F.kernel_positive hReserve hSmall x U hVacuum

end YM.Integration.FullQLocal.RenderedStep.Numeric
end
