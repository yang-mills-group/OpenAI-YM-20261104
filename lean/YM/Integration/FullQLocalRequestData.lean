import YM.Integration.LocalComparisonGlobalContract
import YM.Integration.ActualRepeatedNorm

/-!
Finite requests and numerical schedules for the separate rendered-step view.
The support exponents are independently positive. Their one-step relation is
paid by the actual blocking geometry; no same-row norm enlargement is asserted.
Analytic width loss remains separate. Legacy records map into these records
without changing their data; there is no reverse grant or target implication.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep
open Filter Lattice Wilson RG Marker LocalComparison
open scoped Topology BigOperators

variable {G : Gauge} {V : Type} {C : Family G}

/-- All fixed finite request data precede widths and output constants. -/
structure Request (V : Type) where
  order : ℕ
  order_ge_two : 2 ≤ order
  eta : ℝ
  eta_pos : 0 < eta
  eta_lt_half : eta < 1 / 2
  inputHorizon : ℕ
  outputHorizon : ℕ
  inputWeight : V → ℕ
  outputWeight : V → ℕ
  input_weight_le v : inputWeight v ≤ inputHorizon
  output_weight_le v : outputWeight v ≤ outputHorizon
  inputFieldOrder : ℕ
  outputFieldOrder : ℕ
  field_minimum : 6 ≤ outputFieldOrder
  inputDistanceOrder : ℕ
  outputDistanceOrder : ℕ
  distance_minimum : 2 ≤ outputDistanceOrder
  field_reserve : outputFieldOrder ≤ inputFieldOrder
  distance_reserve : outputDistanceOrder ≤ inputDistanceOrder
  input_engineering : inputHorizon ≤ inputFieldOrder
  output_engineering : outputHorizon ≤ outputFieldOrder
  spareSupport : ℝ
  spare_support_positive : 0 < spareSupport
  reserveFugacity : ℝ
  reserve_fugacity_nonnegative : 0 ≤ reserveFugacity
  reserve_fugacity_lt_one : reserveFugacity < 1
  inputSupport : ℝ
  outputSupport : ℝ
  output_support_pos : 0 < outputSupport
  input_support_pos : 0 < inputSupport
  tests : V → ComparisonDensity.Address.Orbit
  test_order v : max (inputWeight v) (outputWeight v) + 2 ≤ (tests v).D
  inheritedConstant : ℝ
  inherited_constant_nonnegative : 0 ≤ inheritedConstant
  physicalPeriodLower : ℝ
  physical_period_nonnegative : 0 ≤ physicalPeriodLower
  vacuumRankCap : ℕ
  inputPacketRankCap : ℕ
  outputPacketRankCap : ℕ
  inputPacketPowerCap : ℕ
  outputPacketPowerCap : ℕ
  forcedConstant : ℝ
  forced_constant_nonnegative : 0 ≤ forcedConstant

/-- Equality at repeated joins is a restriction of finite requested orders,
not a claim that a weaker produced norm can be enlarged. -/
structure SameNorm (J : Request V) : Prop where
  field_order : J.outputFieldOrder = J.inputFieldOrder
  distance_order : J.outputDistanceOrder = J.inputDistanceOrder
  support : J.outputSupport = J.inputSupport

/-- The original level supplies threshold and cover scale. Numerical width,
cost and flatness receipts retain their complete original formulas. -/
structure Schedule (C : Family G) (J : Request V) where
  inputNorm : ℕ → BudgetPoint
  outputNorm : ℕ → BudgetPoint
  input_norm m : NormAt C (m + 1) (inputNorm m)
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport
  output_norm m : NormAt C m (outputNorm m)
    J.outputFieldOrder J.outputDistanceOrder J.outputSupport
  inputWidth : ℕ → ℝ
  outputWidth : ℕ → ℝ
  input_width_pos m : 0 < inputWidth m
  output_width_pos m : 0 < outputWidth m
  width_reserve m : outputWidth m < inputWidth m
  admittedCost : ℕ → ℝ
  admitted_cost_nonnegative m : 0 ≤ admittedCost m
  admitted_cost_ge_one m : 1 ≤ admittedCost m
  radiusLoss : ℕ → ℝ
  radius_loss_positive m : 0 < radiusLoss m
  radius_loss_ge_one m : 1 ≤ radiusLoss m
  calibrationCap : ℕ → ℝ
  calibration_cap_nonnegative m : 0 ≤ calibrationCap m
  calibration_cap_tendsto : Tendsto calibrationCap atTop (𝓝 0)
  cost_covers_widths m : (inputWidth m)⁻¹ + (outputWidth m)⁻¹ +
    radiusLoss m ≤ admittedCost m
  cost_covers_geometry m :
    1 + (C.path.levels.clock.coverSize m : ℝ) +
      (C.path.levels.clock.coverSize (m + 1) : ℝ) +
      C.path.levels.clock.monitor m + C.path.levels.clock.monitor (m + 1) +
      C.path.levels.clock.loopCap m + C.path.levels.clock.loopCap (m + 1) +
      (C.path.levels.params m).paths + (C.path.levels.params (m + 1)).paths +
      (C.path.levels.params m).columns + (C.path.levels.params (m + 1)).columns +
      (C.path.levels.params m).clip.relaxation +
      (C.path.levels.params (m + 1)).clip.relaxation ≤ admittedCost m
  cost_covers_units m N period (hm : m < N) :
    C.path.levels.clock.threshold m /
        Pert.Asymptotics.regulatorRun C N period (m + 1) +
      C.path.levels.clock.threshold (m + 1) /
        Pert.Asymptotics.regulatorRun C N period (m + 1) ≤ admittedCost m
  cost_subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      admittedCost m ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) ^ (-epsilon)
  pathRate : ℕ → ℝ
  path_rate_positive m : 0 < pathRate m
  path_rate_width m : pathRate m ≤ min (inputWidth m) (outputWidth m)
  path_rate_cost m : (pathRate m)⁻¹ ≤ admittedCost m
  regular_flat (costPower couplingPower targetPower : ℕ) :
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      admittedCost m ^ costPower *
        (Pert.Asymptotics.regulatorRun C N period (m + 1)) ^ (-(couplingPower : ℝ)) *
        Real.exp (-pathRate m * (C.path.levels.clock.coverSize m : ℝ)) ≤
      (Pert.Asymptotics.regulatorRun C N period (m + 1)) ^ targetPower
  forced_flat (delta : ℝ) (hdelta : 0 < delta)
      (costPower couplingPower denominatorPower targetPower : ℕ) :
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      admittedCost m ^ costPower *
        (Pert.Asymptotics.regulatorRun C N period (m + 1)) ^ (-(couplingPower : ℝ)) *
        Real.exp (-pathRate m * (C.path.levels.clock.monitor m) ^ delta /
          (1 + (C.path.levels.clock.coverSize m : ℝ)) ^ denominatorPower) ≤
      (Pert.Asymptotics.regulatorRun C N period (m + 1)) ^ targetPower

variable {J : Request V}

structure Prices (A : Schedule C J) where
  vacuumConstant : ℝ
  vacuum_constant_nonnegative : 0 ≤ vacuumConstant
  markedConstant : ℝ → ℝ
  marked_constant_nonnegative delta : 0 < delta → 0 ≤ markedConstant delta
  vanishing : ℕ → ℝ
  vanishing_nonnegative m : 0 ≤ vanishing m
  vanishing_tendsto : Tendsto vanishing atTop (𝓝 0)
  geometry : ℕ → ℝ
  geometry_nonnegative m : 0 ≤ geometry m
  polynomialConstant : ℝ
  polynomial_constant_nonnegative : 0 ≤ polynomialConstant
  polynomialDegree : ℕ
  polynomial_bound m : geometry m ≤
    polynomialConstant * (1 + A.admittedCost m) ^ polynomialDegree
  hullMultiplier : ℕ → ℕ
  hull_positive m : 0 < hullMultiplier m
  hull_bound m : (hullMultiplier m : ℝ) ≤
    polynomialConstant * (1 + A.admittedCost m) ^ polynomialDegree
  subpower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      geometry m ≤
        Pert.Asymptotics.regulatorRun C N period (m + 1) ^ (-epsilon)

/-- One-way data projection from the stricter legacy finite request. -/
def Request.fromLegacy (J : LocalComparison.Global.Setup V) : Request V where
  order := J.order
  order_ge_two := J.order_ge_two
  eta := J.eta
  eta_pos := J.eta_pos
  eta_lt_half := J.eta_lt_half
  inputHorizon := J.inputHorizon
  outputHorizon := J.outputHorizon
  inputWeight := J.inputWeight
  outputWeight := J.outputWeight
  input_weight_le := J.input_weight_le
  output_weight_le := J.output_weight_le
  inputFieldOrder := J.inputFieldOrder
  outputFieldOrder := J.outputFieldOrder
  field_minimum := J.field_minimum
  inputDistanceOrder := J.inputDistanceOrder
  outputDistanceOrder := J.outputDistanceOrder
  distance_minimum := J.distance_minimum
  field_reserve := J.field_reserve
  distance_reserve := J.distance_reserve
  input_engineering := J.input_engineering
  output_engineering := J.output_engineering
  spareSupport := J.spareSupport
  spare_support_positive := J.spare_support_positive
  reserveFugacity := J.reserveFugacity
  reserve_fugacity_nonnegative := J.reserve_fugacity_nonnegative
  reserve_fugacity_lt_one := J.reserve_fugacity_lt_one
  inputSupport := J.inputSupport
  outputSupport := J.outputSupport
  output_support_pos := J.output_support_pos
  input_support_pos := J.output_support_pos.trans J.support_reserve
  tests := J.tests
  test_order := J.test_order
  inheritedConstant := J.inheritedConstant
  inherited_constant_nonnegative := J.inherited_constant_nonnegative
  physicalPeriodLower := J.physicalPeriodLower
  physical_period_nonnegative := J.physical_period_nonnegative
  vacuumRankCap := J.vacuumRankCap
  inputPacketRankCap := J.inputPacketRankCap
  outputPacketRankCap := J.outputPacketRankCap
  inputPacketPowerCap := J.inputPacketPowerCap
  outputPacketPowerCap := J.outputPacketPowerCap
  forcedConstant := J.forcedConstant
  forced_constant_nonnegative := J.forced_constant_nonnegative

/-- All numerical schedules and their actual-level conventions are preserved. -/
def Schedule.fromLegacy {J : LocalComparison.Global.Setup V}
    (A : LocalComparison.Global.Admission C J) :
    Schedule C (Request.fromLegacy J) where
  inputNorm := A.inputNorm
  outputNorm := A.outputNorm
  input_norm := A.input_norm
  output_norm := A.output_norm
  inputWidth := A.inputWidth
  outputWidth := A.outputWidth
  input_width_pos := A.input_width_pos
  output_width_pos := A.output_width_pos
  width_reserve := A.width_reserve
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

def Prices.fromLegacy {J : LocalComparison.Global.Setup V}
    {A : LocalComparison.Global.Admission C J}
    (K : LocalComparison.Global.Prices A) : Prices (Schedule.fromLegacy A) where
  vacuumConstant := K.vacuumConstant
  vacuum_constant_nonnegative := K.vacuum_constant_nonnegative
  markedConstant := K.markedConstant
  marked_constant_nonnegative := K.marked_constant_nonnegative
  vanishing := K.vanishing
  vanishing_nonnegative := K.vanishing_nonnegative
  vanishing_tendsto := K.vanishing_tendsto
  geometry := K.geometry
  geometry_nonnegative := K.geometry_nonnegative
  polynomialConstant := K.polynomialConstant
  polynomial_constant_nonnegative := K.polynomial_constant_nonnegative
  polynomialDegree := K.polynomialDegree
  polynomial_bound := K.polynomial_bound
  hullMultiplier := K.hullMultiplier
  hull_positive := K.hull_positive
  hull_bound := K.hull_bound
  subpower := K.subpower

/-- The upper output and next lower input are literally the same norm at
their shared physical level. The geometric reserve is proved separately by
ActualRepeatedNorm.eventually_geometry on this same original trajectory. -/
theorem Schedule.adjacent_norm (A : Schedule C J) (hJ : SameNorm J) (m : ℕ) :
    A.outputNorm (m+1) = A.inputNorm m := by
  have hout : LocalComparison.NormAt C (m+1) (A.outputNorm (m+1))
      J.inputFieldOrder J.inputDistanceOrder J.inputSupport := by
    simpa only [hJ.field_order, hJ.distance_order, hJ.support] using A.output_norm (m+1)
  have hi := A.input_norm m
  exact
    (ActualRepeatedNorm.norm_unique C J.inputFieldOrder J.inputDistanceOrder
      J.inputSupport (J.field_minimum.trans J.field_reserve)
      (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
      (m+1) (A.outputNorm (m+1)) hout).trans
    (ActualRepeatedNorm.norm_unique C J.inputFieldOrder J.inputDistanceOrder
      J.inputSupport (J.field_minimum.trans J.field_reserve)
      (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
      (m+1) (A.inputNorm m) hi).symm

end YM.Integration.FullQLocal.RenderedStep
end
