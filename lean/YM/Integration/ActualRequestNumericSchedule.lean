import YM.Integration.ActualRunQLocalAdmission
import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.ActualBoundedNumericSchedule

/-!
The literal requested-norm numerical schedule for a selected pre-block width
family. This ports the already-proved admission fields to Request, whose input
and output support exponents are independently positive. No strict comparison
between those exponents is introduced. The final input strip is clipped by
the existing bounded-schedule constructor before any analytic input is chosen.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRequestNumericSchedule
open Filter Lattice RG FullQLocal FullQLocal.RenderedStep
open PhysicalNext.Repeat.Legato
open ActualRunAdmissionScales ActualRunComponentAdmission
open scoped Topology

variable {G : Gauge} {V : Type}

/-- The original numerical admission proof with the exact Request fields. -/
def ofPayment (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (hMesh : ActualRunAdmissionClock.PreMesh C.path.levels)
    (W : ProfileWidths) (P : WidthPayment C W) (J : Request V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) : NumericSchedule C J where
  inputNorm m := requestedBudget C.path.levels (m+1) J.inputFieldOrder
    J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
  outputNorm m := requestedBudget C.path.levels m J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum J.output_support_pos
  input_norm m := requested_norm C (m+1) J.inputFieldOrder
    J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
  output_norm m := requested_norm C m J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum J.output_support_pos
  inputWidth := W.pair C
  outputWidth m := W.pair C m / 2
  input_width_pos := W.pair_positive C
  output_width_pos m := div_pos (W.pair_positive C m) (by norm_num)
  admittedCost := cost C W
  admitted_cost_nonnegative m := zero_le_one.trans (cost_one C W m)
  admitted_cost_ge_one := cost_one C W
  radiusLoss _ := 1
  radius_loss_positive _ := zero_lt_one
  radius_loss_ge_one _ := le_rfl
  calibrationCap := cap
  calibration_cap_nonnegative := hcap
  calibration_cap_tendsto := hcap0
  cost_covers_widths := cost_width C W
  cost_covers_geometry m :=
    (ActualRunAdmissionScales.cost_covers_geometry C.path.levels m).trans (cost_ge_native C W m)
  cost_covers_units m N period hm :=
    (ActualRunAdmissionScales.cost_covers_units C hC m N period hm).trans (cost_ge_native C W m)
  cost_subpower ε hε := eventually_atTop.1
    (ActualRunComponentAdmission.cost_subpower C W P hG hC hMesh ε hε)
  pathRate := rate C W
  path_rate_positive := rate_pos C W
  path_rate_width m := by
    have hp := W.pair_positive C m
    rw [min_eq_right (show W.pair C m / 2 ≤ W.pair C m by linarith)]
    exact rate_width C W m
  path_rate_cost := rate_cost C W
  regular_flat a c t := eventually_atTop.1
    (ActualRunComponentAdmission.regular_flat C W P hG hC hMesh a c t)
  forced_flat δ hδ a c d t := eventually_atTop.1
    (ActualRunComponentAdmission.forced_flat C W P hG hC hMesh δ hδ a c d t)

/-- The original Run supplies Makes and its retained preMesh purchase. -/
def atRun (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (W : ProfileWidths) (P : WidthPayment R.family W) (J : Request V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) : NumericSchedule R.family J :=
  ofPayment R.family hG R.makes
    (ActualRunQLocalAdmission.actual_preMesh R hReadout) W P J cap hcap hcap0

/-- This is the sole schedule used by the pre-Run qlocal projection below. -/
def selected (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (W : ProfileWidths) (P : WidthPayment R.family W) (J : Request V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) : NumericSchedule R.family J :=
  ActualBoundedNumericSchedule.bounded R hG
    (atRun R hG hReadout W P J cap hcap hcap0)

theorem selected_input_le_one (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (W : ProfileWidths) (P : WidthPayment R.family W) (J : Request V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    (selected R hG hReadout W P J cap hcap hcap0).inputWidth m ≤ 1 :=
  ActualBoundedNumericSchedule.input_width_le_one R hG _ m

end YM.Integration.ActualRequestNumericSchedule
end
