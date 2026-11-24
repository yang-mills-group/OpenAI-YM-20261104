import YM.Integration.ActualQlocalNaturalRequests

/-! Exact finite relabeling of Request and Schedule.
Every scalar, support, width, cost and actual-level tail stays on the same
family. Independent tests are transported pointwise. This is a data
isomorphism, not a cofinality or analytic existence theorem. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualQlocalRequestTransport
open Lattice Wilson RG LocalComparison FullQLocal.RenderedStep
open scoped Classical

variable {V W : Type}

def reindex (e : W ≃ V) (J : Request V) : Request W where
  order := J.order
  order_ge_two := J.order_ge_two
  eta := J.eta
  eta_pos := J.eta_pos
  eta_lt_half := J.eta_lt_half
  inputHorizon := J.inputHorizon
  outputHorizon := J.outputHorizon
  inputWeight := fun w => J.inputWeight (e w)
  outputWeight := fun w => J.outputWeight (e w)
  input_weight_le := fun w => J.input_weight_le (e w)
  output_weight_le := fun w => J.output_weight_le (e w)
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
  input_support_pos := J.input_support_pos
  tests := fun w => J.tests (e w)
  test_order := fun w => J.test_order (e w)
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

theorem reindex_symm (e : W ≃ V) (J : Request V) :
    reindex e.symm (reindex e J) = J := by
  cases J
  simp only [reindex, Equiv.apply_symm_apply]

theorem scalarCode_reindex (e : W ≃ V) (J : Request V) :
    ActualQlocalNaturalRequests.scalarCode (reindex e J) =
      ActualQlocalNaturalRequests.scalarCode J := rfl

theorem slotCode_reindex (e : W ≃ V) (J : Request V) (w : W) :
    ActualQlocalNaturalRequests.slotCode (reindex e J) w =
      ActualQlocalNaturalRequests.slotCode J (e w) := rfl

def tests (e : W ≃ V) (J : Request V) :
    TestSpace J.tests ≃ TestSpace (reindex e J).tests :=
  (Equiv.piCongrLeft (fun v => (J.tests v).Mood) e).symm

def unitTests (e : W ≃ V) (J : Request V) :
    IndependentTests J.tests ≃ IndependentTests (reindex e J).tests :=
  (Equiv.piCongrLeft
    (fun v => {f : ComparisonDensity.Address.Pos → ℂ // (J.tests v).Bill f 1}) e).symm

theorem tests_apply (e : W ≃ V) (J : Request V)
    (x : TestSpace J.tests) (w : W) :
    tests e J x w = x (e w) := rfl

theorem test_inclusion (e : W ≃ V) (J : Request V)
    (x : IndependentTests J.tests) :
    tests e J (testInclusion J.tests x) =
      testInclusion (reindex e J).tests (unitTests e J x) := by
  funext w
  rfl

theorem sameNorm (e : W ≃ V) (J : Request V) (hJ : SameNorm J) :
    SameNorm (reindex e J) :=
  ⟨hJ.field_order, hJ.distance_order, hJ.support⟩

variable {G : Gauge} {C : Family G} {J : Request V}

def schedule (e : W ≃ V) (A : YM.Integration.FullQLocal.RenderedStep.Schedule C J) : YM.Integration.FullQLocal.RenderedStep.Schedule C (reindex e J) where
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

theorem schedule_data (e : W ≃ V) (A : YM.Integration.FullQLocal.RenderedStep.Schedule C J) :
    (schedule e A).inputNorm = A.inputNorm ∧
    (schedule e A).outputNorm = A.outputNorm ∧
    (schedule e A).inputWidth = A.inputWidth ∧
    (schedule e A).outputWidth = A.outputWidth ∧
    (schedule e A).admittedCost = A.admittedCost ∧
    (schedule e A).radiusLoss = A.radiusLoss ∧
    (schedule e A).calibrationCap = A.calibrationCap ∧
    (schedule e A).pathRate = A.pathRate :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end YM.Integration.ActualQlocalRequestTransport
end
