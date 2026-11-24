import YM.Integration.LocalComparisonInterface
import YM.Planned.CALIBRATED_MIXED_HISTORY.Bridge
import YM.Push.CORRECTED_COLUMNS.Grows
import YM.Extra.ITERATION_NO_LOSS.Geometry

/-!
A single inherited norm on the original trajectory. Input at m+1 and output
at m use the same finite orders and support exponent; their actual threshold
and cover scale remain those of the original level. A separate finite internal
support reserve is paid by the actual growing block factor. The inherited norm keeps the geometry at each original level.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRepeatedNorm
open Filter Lattice Lattice.Corona Wilson RG
open scoped Topology BigOperators

variable {G : Gauge} (C : Family G)
    (fieldOrder distanceOrder : ℕ) (support : ℝ)
    (hfield : 6 ≤ fieldOrder) (hdistance : 2 ≤ distanceOrder) (hsupport : 0 < support)

/-- Only the requested finite norm parameters change; the level is literal. -/
def atLevel (level : ℕ) : BudgetPoint :=
  { C.path.levels.budget level with
    order := fieldOrder
    power := distanceOrder
    supportExponent := support
    order_ge := hfield
    power_ge := hdistance
    exponent_pos := hsupport }

theorem norm_at (level : ℕ) :
    LocalComparison.NormAt C level
      (atLevel C fieldOrder distanceOrder support hfield hdistance hsupport level)
      fieldOrder distanceOrder support :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The full norm is determined by its original-level convention receipt. -/
theorem norm_unique (level : ℕ) (Q : BudgetPoint)
    (hQ : LocalComparison.NormAt C level Q fieldOrder distanceOrder support) :
    Q = atLevel C fieldOrder distanceOrder support hfield hdistance hsupport level := by
  rcases Q with ⟨qp, qo, qs, qB, qt, hqp, hqo, hqs, hqB, hqt, hqle⟩
  rcases hQ with ⟨ht, hB, ho, hp, hs⟩
  dsimp only at ht hB ho hp hs
  subst qp
  subst qo
  subst qs
  subst qB
  subst qt
  rfl

/-- One actual tail pays every period and every later support/test choice. -/
theorem eventually_geometry (hG : G.Simple) (padding : ℕ) (extra : ℝ)
    (hextra : 0 ≤ extra) :
    ∀ᶠ m : ℕ in atTop, ∀ period : ℕ,
      Extra.Iteration.Shapes.raw (C.path.levels.clock.op m period).ratio padding
        (atLevel C fieldOrder distanceOrder support hfield hdistance hsupport (m+1))
        (atLevel C fieldOrder distanceOrder support hfield hdistance hsupport m) extra := by
  let K := (20 : ℝ) * Extra.Iteration.Shapes.pad (padding+9) * (support+extra)
  have hL := (Planned.CalibratedMixedHistory.Bridge.reach C.path.levels).eventually_ge_atTop
    (K / support)
  have hB := Push.Corrected.Grows.walls C.path.levels hG 1
  filter_upwards [hL, hB] with m hm hcover period
  refine ⟨?_, hextra, ?_⟩
  · change C.path.levels.clock.coverSize (m+1) ≤ 2*C.path.levels.clock.coverSize m
    simpa only [pow_one] using hcover
  · change K ≤ support * ((C.S.block m).val : ℝ)
    exact ((div_le_iff₀ hsupport).mp hm).trans_eq (mul_comm _ _)

/-- Complete inspected supports keep the unused half of the incoming weight.
The scalar t is the original row majorant and is never chosen from its value. -/
theorem eventually_support (hG : G.Simple) (padding : ℕ) (extra : ℝ)
    (hextra : 0 ≤ extra) :
    ∀ᶠ m : ℕ in atTop, ∀ period : ℕ,
      ∀ (X : Support (C.side (m+1) period)) (Y : Support (C.side m period)),
      Y ⊆ halo (padding * (C.path.levels.budget m).B)
        ((inspected X).image (C.path.levels.clock.op m period).ratio.parent) →
      ∀ t : ℝ, 0 ≤ t →
        Mix.loaf (atLevel C fieldOrder distanceOrder support hfield hdistance hsupport m)
          Y extra t ≤
        Real.exp (Extra.Iteration.Shapes.pad (padding+9) * (support+extra)) *
          Real.exp (-(support/2) *
            (coverNumber (C.path.levels.budget (m+1)).B X : ℝ)) *
          (atLevel C fieldOrder distanceOrder support hfield hdistance hsupport (m+1)).mass X t := by
  filter_upwards [eventually_geometry C fieldOrder distanceOrder support
    hfield hdistance hsupport hG padding extra hextra] with m hm period X Y hY t ht
  exact Extra.Iteration.Shapes.reserve (hm period) hY ht

end YM.Integration.ActualRepeatedNorm
end
