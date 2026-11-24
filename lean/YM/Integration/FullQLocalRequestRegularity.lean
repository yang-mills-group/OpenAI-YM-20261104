import YM.Integration.ActualQlocalRequestFamily
import YM.Integration.ActualRequestNumericSchedule

/-!
A finite regularity closure chosen before the complete qlocal witness.
It changes only the requested field/distance orders and support exponents.
The original request has a literal numerical projection with identical
physical family, widths, costs, radii, calibration cap and flatness duties.
This file does not project a Grant or choose any new Run or model.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocalRequestRegularity
open Filter Lattice RG FullQLocal FullQLocal.RenderedStep
open PhysicalNext.Repeat.Legato
open scoped Topology

variable {G : Gauge} {V : Type} {C : Family G}

/-- Equal internal regularity on both ends, dominating the original norms. -/
def close (J : Request V) : Request V :=
  { J with
    outputFieldOrder := J.inputFieldOrder
    field_minimum := J.field_minimum.trans J.field_reserve
    outputDistanceOrder := J.inputDistanceOrder
    distance_minimum := J.distance_minimum.trans J.distance_reserve
    field_reserve := le_rfl
    distance_reserve := le_rfl
    output_engineering := J.output_engineering.trans J.field_reserve
    inputSupport := max J.inputSupport J.outputSupport
    outputSupport := max J.inputSupport J.outputSupport
    input_support_pos := J.input_support_pos.trans_le (le_max_left _ _)
    output_support_pos := J.output_support_pos.trans_le (le_max_right _ _) }

theorem close_sameNorm (J : Request V) : SameNorm (close J) :=
  ⟨rfl, rfl, rfl⟩

/-- The old request, with all numerical data copied from the stronger one. -/
def originalSchedule (J : Request V) (A : NumericSchedule C (close J)) :
    NumericSchedule C J where
  inputNorm m := ActualRepeatedNorm.atLevel C J.inputFieldOrder
    J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos (m + 1)
  outputNorm m := ActualRepeatedNorm.atLevel C J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport
    J.field_minimum J.distance_minimum J.output_support_pos m
  input_norm m := ActualRepeatedNorm.norm_at C J.inputFieldOrder
    J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos (m + 1)
  output_norm m := ActualRepeatedNorm.norm_at C J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport
    J.field_minimum J.distance_minimum J.output_support_pos m
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

/-- The precise five-field restriction needed by native norm transport. -/
theorem input_restrict (J : Request V) (A : NumericSchedule C (close J)) (m : ℕ) :
    ((originalSchedule J A).inputNorm m).threshold = (A.inputNorm m).threshold ∧
    ((originalSchedule J A).inputNorm m).B = (A.inputNorm m).B ∧
    ((originalSchedule J A).inputNorm m).order ≤ (A.inputNorm m).order ∧
    ((originalSchedule J A).inputNorm m).power ≤ (A.inputNorm m).power ∧
    ((originalSchedule J A).inputNorm m).supportExponent ≤
      (A.inputNorm m).supportExponent := by
  refine ⟨(A.input_norm m).threshold.symm, (A.input_norm m).block.symm, ?_, ?_, ?_⟩
  · change J.inputFieldOrder ≤ (A.inputNorm m).order
    rw [(A.input_norm m).order]
    exact le_rfl
  · change J.inputDistanceOrder ≤ (A.inputNorm m).power
    rw [(A.input_norm m).distance]
    exact le_rfl
  · change J.inputSupport ≤ (A.inputNorm m).supportExponent
    rw [(A.input_norm m).reserve]
    exact le_max_left _ _

theorem output_restrict (J : Request V) (A : NumericSchedule C (close J)) (m : ℕ) :
    ((originalSchedule J A).outputNorm m).threshold = (A.outputNorm m).threshold ∧
    ((originalSchedule J A).outputNorm m).B = (A.outputNorm m).B ∧
    ((originalSchedule J A).outputNorm m).order ≤ (A.outputNorm m).order ∧
    ((originalSchedule J A).outputNorm m).power ≤ (A.outputNorm m).power ∧
    ((originalSchedule J A).outputNorm m).supportExponent ≤
      (A.outputNorm m).supportExponent := by
  refine ⟨(A.output_norm m).threshold.symm, (A.output_norm m).block.symm, ?_, ?_, ?_⟩
  · change J.outputFieldOrder ≤ (A.outputNorm m).order
    rw [(A.output_norm m).order]
    exact J.field_reserve
  · change J.outputDistanceOrder ≤ (A.outputNorm m).power
    rw [(A.output_norm m).distance]
    exact J.distance_reserve
  · change J.outputSupport ≤ (A.outputNorm m).supportExponent
    rw [(A.output_norm m).reserve]
    exact le_max_right _ _

/-- Equality is proved for the internal request, without a final SameNorm premise. -/
theorem adjacent_norm (J : Request V) (A : NumericSchedule C (close J)) (m : ℕ) :
    A.outputNorm (m + 1) = A.inputNorm m :=
  A.adjacent_norm (close_sameNorm J) m

/-- No price, geometric factor or tail is changed by the numerical projection. -/
def originalPrices (J : Request V) {A : NumericSchedule C (close J)}
    (K : NumericPrices A) : NumericPrices (originalSchedule J A) where
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

/-- The actual selected schedule uses the same Run, width payment and cap.
Only its two requested norms depend on these changed Request fields. -/
theorem selected_original (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (W : ProfileWidths) (P : WidthPayment R.family W) (J : Request V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    originalSchedule J
      (ActualRequestNumericSchedule.selected R hG hReadout W P (close J)
        cap hcap hcap0) =
      ActualRequestNumericSchedule.selected R hG hReadout W P J cap hcap hcap0 := rfl

/-- A single fixed real recipe covers every closed discrete request. -/
def closeRecipe (P : ActualQlocalRequestFamily.Recipe) :
    ActualQlocalRequestFamily.Recipe :=
  { P with
    inputSupport := max P.inputSupport P.outputSupport
    outputSupport := max P.inputSupport P.outputSupport
    input_pos := P.input_pos.trans_le (le_max_left _ _)
    output_pos := P.output_pos.trans_le (le_max_right _ _) }

theorem close_matches (P : ActualQlocalRequestFamily.Recipe) (J : Request V)
    (hP : ActualQlocalRequestFamily.Matches P J) :
    ActualQlocalRequestFamily.Matches (closeRecipe P) (close J) where
  eta := hP.eta
  spare := hP.spare
  fugacity := hP.fugacity
  input := congrArg₂ max hP.input hP.output
  output := congrArg₂ max hP.input hP.output

/-- Enumeration still precedes the sole Run choice. The exact natural cost
cap, finite relabeling and stronger physical-period condition remain. -/
theorem dictionary_complete [Fintype V]
    (P : ActualQlocalRequestFamily.Recipe) (J : Request V)
    (hP : ActualQlocalRequestFamily.Matches P J)
    (hwhole : ∀ v, ∃ d w : ℕ, J.tests v = ⟨.whole, d, w⟩) :
    ∃ e : Fin (Fintype.card V) ≃ V, ∃ j : ℕ,
      ActualQlocalRequestFamily.family (closeRecipe P) j =
        ⟨Fintype.card V, ActualQlocalRequestFamily.capped
          (ActualQlocalRequestTransport.reindex e (close J))⟩ :=
  ActualQlocalRequestFamily.complete_finite (closeRecipe P) (close J)
    (close_matches P J hP) hwhole

end YM.Integration.FullQLocalRequestRegularity
end
