import YM.Integration.FullQLocalRequestData

/-!
A numerical projection of the preserved rendered-step Schedule.
Only the extra strict input/output width comparison is omitted. All actual
norms, costs, flatness estimates and before-cutoff/period quantifiers remain.
The actual shared widths and native component windows must be constructed
separately before the full qlocal application. This record is not that grant.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep
open Filter Lattice Wilson RG Marker LocalComparison
open scoped Topology BigOperators

variable {G : Gauge} {V : Type} {C : Family G}

/-- Numerical receipts without a postulated strict loss between the two strips. -/
structure NumericSchedule (C : Family G) (J : Request V) where
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

structure NumericPrices (A : NumericSchedule C J) where
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

/-- Forget only the preserved v2 Schedule's extra strict width comparison. -/
def Schedule.toNumeric (A : Schedule C J) : NumericSchedule C J where
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

/-- The complete original price data and their numerical bounds are unchanged. -/
def Prices.toNumeric {A : Schedule C J} (K : Prices A) :
    NumericPrices A.toNumeric where
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

/-- Equality of adjacent norms is independent of any analytic strip comparison. -/
theorem NumericSchedule.adjacent_norm (A : NumericSchedule C J) (hJ : SameNorm J) (m : ℕ) :
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
