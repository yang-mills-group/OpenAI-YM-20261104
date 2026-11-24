import YM.Integration.LocalComparisonGlobalContract

/-!
# Retained marked inputs and their separate preparation receipts

An actual calibration coefficient can contain a countable regular remainder.
This file keeps its complete represented marked input and full regular/forced
price. It does not identify such an input with a finite analytic packet bank.

`PreparedWithRemainder` is an additional, explicit factorization receipt. Its
factorization and price include every regular, unit, caption and forced channel
of the remainder. In particular, subtracting an unmasked analytic packet from
a masked native section can create a compensating forced contribution; this
receipt does not construct that contribution or infer its price.

These are internal application interfaces. No comparison conclusion is asserted
for them. The literal analytic `Prepared` embeds into this interface, and the
reverse adapter requires the exact zero-channel hypotheses rather than deriving
them from Format, remBound, or a zero numerical regular allowance. All data are
whole functionals, chosen before the independent test tuple.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.Global

open Lattice Wilson RG Marker
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G}

/-- A full represented marked input with a full price on the same carrier.
There is no finite-bank, zero-remainder, or unconditional marked-support
restriction here. Those are separate preparation or geometric obligations. -/
structure RetainedMarkedInput {D : V → ComparisonDensity.Address.Orbit}
    (N period level : ℕ) (Q : StepCarrier C N period level)
    (roots : V → Site (C.side level period))
    (w : V → ℝ) (kernelEnvelope : R.Mode → ℝ)
    (regularPrice forcedPrice : ℝ) where
  value : Taste (TestSpace D) roots Q.rep R
  multilinear : Multilinear D value
  price : RelativeBudget (C.path.levels.budget level)
    (pullback (testInclusion D) value) w (forcedDivisor C level)
    kernelEnvelope regularPrice forcedPrice

/-- A factorization of one complete input, allowing its remainder to retain
all original channels. This is a receipt to prove in the application, not an
additional conclusion of the external local-comparison lemma. -/
structure PreparedWithRemainder {D : V → ComparisonDensity.Address.Orbit}
    (N period level : ℕ) (Q : StepCarrier C N period level)
    (roots : V → Site (C.side level period))
    (input : Taste (TestSpace D) roots Q.rep R)
    (colors : TestSpace D → Bulk.Colors R G (C.side level period))
    (packets : MarkedPackets D G (C.side level period) R)
    (w : V → ℝ) (kernelEnvelope : R.Mode → ℝ)
    (regularPrice forcedPrice : ℝ) where
  convention : InputColors colors packets
  remainder : Taste (TestSpace D) roots Q.rep R
  full (x : TestSpace D) (U : Config G (C.side level period)) :
    (input.leaf x).density U =
      Poly.pass (packets.read x (Pert.Asymptotics.regulatorRun C N period level) U) *
        (remainder.leaf x).density U
  remainder_price : RelativeBudget (C.path.levels.budget level)
    (pullback (testInclusion D) remainder) w (forcedDivisor C level)
    kernelEnvelope regularPrice forcedPrice

variable {D : V → ComparisonDensity.Address.Orbit}
    {N period level : ℕ} {Q : StepCarrier C N period level}
    {roots : V → Site (C.side level period)}
    {input : Taste (TestSpace D) roots Q.rep R}
    {colors : TestSpace D → Bulk.Colors R G (C.side level period)}
    {packets : MarkedPackets D G (C.side level period) R}
    {w : V → ℝ} {kernelEnvelope : R.Mode → ℝ} {forcedPrice : ℝ}

/-- The analytic preparation retains exactly its same represented remainder
when regarded as a general preparation receipt. -/
def Prepared.withRemainder
    (h : Prepared N period level Q roots input colors packets w kernelEnvelope forcedPrice) :
    PreparedWithRemainder N period level Q roots input colors packets w kernelEnvelope
      0 forcedPrice where
  convention := h.convention
  remainder := h.remainder
  full := h.full
  remainder_price := h.forced_price

/-- Returning to the literal analytic inlet requires actual zero channels.
A numerical price or a projection of the input does not replace these facts. -/
def PreparedWithRemainder.toLiteral
    (h : PreparedWithRemainder N period level Q roots input colors packets w
      kernelEnvelope 0 forcedPrice)
    (hRegular : ∀ x i, h.remainder.menu.regular x i = 0)
    (hUnit : ∀ x v, h.remainder.menu.global x v = 0)
    (hCaption : ∀ x i, h.remainder.score x i = 0) :
    Prepared N period level Q roots input colors packets w kernelEnvelope forcedPrice where
  convention := h.convention
  remainder := h.remainder
  regular_zero := hRegular
  unit_zero := hUnit
  caption_zero := hCaption
  full := h.full
  forced_price := h.remainder_price

end YM.Integration.LocalComparison.Global
