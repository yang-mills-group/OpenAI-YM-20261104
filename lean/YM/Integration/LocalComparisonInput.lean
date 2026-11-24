import YM.Integration.LocalComparisonPackets
import YM.Integration.LocalComparisonEnvelope
import YM.Comparison.RG02.Integral.Model
import YM.Pert.Asymptotics.RawAxis

/-! The analytic marked input convention of the local-comparison interface.

This is an explicitly prepared input, not an assertion that an arbitrary
physical source already has this form. In particular, passing from masked
packets to the full-group rendering must retain and pay the actual forced
partners. The nonanalytic inherited vacuum error is never placed inside
`Bulk.Colors` by this definition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker RG3.Script.Picnic
open Comparison.RG02

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {C : Family G} {D : V → ComparisonDensity.Address.Orbit}

/-- The exact native `Colors` normalization: its raw mark of grade `power`
is divided by that coupling power before it is the physical logarithmic
packet. This ties the independent formal inputs to the literal real model,
including every nonzero coupling value, not merely a finite jet. -/
structure InputColors {n : Side}
    (colors : TestSpace D → Bulk.Colors R G n)
    (packets : MarkedPackets D G n R) : Prop where
  well x : Bulk.Well (colors x)
  vacuum x y : (colors x).vac = (colors y).vac
  power x y : (colors x).power = (colors y).power
  marks (x : TestSpace D) (g : ℝ) (hg : g ≠ 0) (U : Config G n) :
    Integral.markedLog g U (colors x) = packets.read x g U

/-- A full marked input after its finite packet-mask attachments have been
paid. The remaining marked terms are forced alternatives on the same
unmarked carrier. Ordinary regular source errors from a previous step are
not declared analytic here; their separate real transmission remains a
separate obligation in the repeated-use clause.
-/
structure PreparedInput (N period level : ℕ)
    (Q : Carrier C N period level) (roots : V → Site (C.side level period))
    (input : Taste (TestSpace D) roots Q.rep R)
    (colors : TestSpace D → Bulk.Colors R G (C.side level period))
    (packets : MarkedPackets D G (C.side level period) R)
    (w : V → ℝ) (kernelEnvelope : R.Mode → ℝ) (forcedPrice : ℝ) where
  convention : InputColors colors packets
  remainder : Taste (TestSpace D) roots Q.rep R
  regular_zero x i : remainder.menu.regular x i = 0
  unit_zero x v : remainder.menu.global x v = 0
  caption_zero x i : remainder.score x i = 0
  full (x : TestSpace D) (U : Config G (C.side level period)) :
    (input.leaf x).density U =
      Poly.pass (packets.read x (Pert.Asymptotics.regulatorRun C N period level) U) *
      (remainder.leaf x).density U
  forced_price : RelativeBudget (C.path.levels.budget level)
    (pullback (testInclusion D) remainder) w (forcedDivisor C level)
    kernelEnvelope 0 forcedPrice

end YM.Integration.LocalComparison
