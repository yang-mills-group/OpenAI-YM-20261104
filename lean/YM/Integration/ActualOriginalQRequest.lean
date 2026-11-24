import YM.Integration.ActualOriginalQLayout
import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.ActualStartupRequestedRemainder
import YM.Integration.ActualRunRequestedNormTail

/-! Finite preselection request choices for the original-Q input.
Only discrete caps and the original chip constant are enlarged. Every
numerical schedule field, width and all-cutoff estimate is preserved. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQRequest
open Filter Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open scoped Classical Topology

variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}
    {V : Type} [DecidableEq V] [Fintype V]
    (u : V → MS.Rake.Label B) (J : Request V)

def request : Request V :=
  { J with
    vacuumRankCap := max J.vacuumRankCap (J.order + 2)
    inputPacketRankCap := max J.inputPacketRankCap (ActualOriginalQLayout.rankCap R u)
    inheritedConstant := max J.inheritedConstant
      ((2 : ℝ) ^ ((J.order : ℝ) + 1 - J.eta))
    inherited_constant_nonnegative :=
      J.inherited_constant_nonnegative.trans (le_max_left _ _) }

/-- No norm, width, price, radius or tail is chosen again. -/
def schedule (A : NumericSchedule R.family J) :
    NumericSchedule R.family (request R u J) where
  inputNorm := A.inputNorm
  outputNorm := A.outputNorm
  input_norm := A.input_norm
  output_norm := A.output_norm
  inputWidth := A.inputWidth
  outputWidth := A.outputWidth
  input_width_pos := A.input_width_pos
  output_width_pos := A.output_width_pos
  admittedCost := A.admittedCost
  admitted_cost_nonnegative := A.admitted_cost_nonnegative
  admitted_cost_ge_one := A.admitted_cost_ge_one
  radiusLoss := A.radiusLoss
  radius_loss_positive := A.radius_loss_positive
  radius_loss_ge_one := A.radius_loss_ge_one
  calibrationCap := A.calibrationCap
  calibration_cap_nonnegative := A.calibration_cap_nonnegative
  calibration_cap_tendsto := A.calibration_cap_tendsto
  cost_covers_widths := A.cost_covers_widths
  cost_covers_geometry := A.cost_covers_geometry
  cost_covers_units := A.cost_covers_units
  cost_subpower := A.cost_subpower
  pathRate := A.pathRate
  path_rate_positive := A.path_rate_positive
  path_rate_width := A.path_rate_width
  path_rate_cost := A.path_rate_cost
  regular_flat := A.regular_flat
  forced_flat := A.forced_flat

omit [DecidableEq V] in
/-- The actual fixed row cap, startup layer cap and complete chip constant
are admitted by the request constructed before the physical input. -/
theorem limits :
    J.order + 2 ≤ (request R u J).vacuumRankCap ∧
    ActualOriginalQLayout.rankCap R u ≤ (request R u J).inputPacketRankCap ∧
    (2 : ℝ) ^ ((J.order : ℝ) + 1 - J.eta) ≤
      (request R u J).inheritedConstant :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

variable (A : NumericSchedule R.family J)

omit [DecidableEq V] in
/-- The full original chip has the requested inherited bound on one tail
before every period, with the unchanged requested norm. -/
theorem eventually_invoice (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ period : ℕ,
      0 ≤ ActualStartupRequestedRemainder.cost R J.order J.eta (m + 1) ∧
      (ActualStartupMaskedAction.remainder R (m + 1) period J.order).Invoice
        ((schedule R u J A).inputNorm m)
        (ActualStartupRequestedRemainder.cost R J.order J.eta (m + 1)) ∧
      ActualStartupRequestedRemainder.cost R J.order J.eta (m + 1) ≤
        (request R u J).inheritedConstant *
          Pert.Asymptotics.regulatorRun R.family (m + 1) period (m + 1) ^
            ((J.order : ℝ) + 1 - J.eta) := by
  have ht := ActualStartupRequestedRemainder.eventual_invoice R hG
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
    J.order J.order_ge_two J.eta J.eta_pos
    (J.eta_lt_half.trans (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht
  filter_upwards [eventually_ge_atTop N] with m hm period
  obtain ⟨hc, hi, hb⟩ := hN (m + 1) (by omega) period
  have he := ActualRepeatedNorm.norm_unique R.family
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
    (m + 1) (A.inputNorm m) (A.input_norm m)
  refine ⟨hc, ?_, hb.trans ?_⟩
  · change (ActualStartupMaskedAction.remainder R (m + 1) period J.order).Invoice
      (A.inputNorm m) _
    rw [he]
    exact hi
  · apply mul_le_mul_of_nonneg_right (limits R u J).2.2
    exact Real.rpow_nonneg
      (RG17.payBand R (p := period) (show m + 1 ≤ m + 1 from le_rfl)).1.le _

omit [DecidableEq V] in
/-- The same schedule also carries the native requested-norm regular cost
on one tail before all cutoffs and periods. -/
theorem eventually_wellFormed
    (hReceipts : StageReceipts R)
    (hprofile : ∀ j, j ≤ (R.metals.p.profile j).order ∧
      j ≤ (R.metals.p.profile j).power)
    (hcap : J.inputSupport ≤ 100) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      ∃ W : LocalComparison.Global.WellFormed
        ((schedule R u J A).inputNorm m)
        (R.family.path.rep N period (m + 1)),
        W.regularCost = R.family.path.levels.clock.allowance (m + 1) := by
  filter_upwards [ActualRunRequestedNormTail.eventually_wellFormed R hReceipts
    hprofile J.inputFieldOrder J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos hcap]
    with m hm N period hN
  have he := ActualRepeatedNorm.norm_unique R.family
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
    (m + 1) (A.inputNorm m) (A.input_norm m)
  change ∃ W : LocalComparison.Global.WellFormed (A.inputNorm m)
      (R.family.path.rep N period (m + 1)),
      W.regularCost = R.family.path.levels.clock.allowance (m + 1)
  rw [he]
  exact hm N period hN

end YM.Integration.ActualOriginalQRequest
end
