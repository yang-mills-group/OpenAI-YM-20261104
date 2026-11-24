import YM.Integration.ActualRunComponentAdmission
import YM.Integration.ActualRunQlocalWidths

/-! Assemble every numerical field of the full-qlocal Admission on the same
Run. WidthPayment and the actual calibration-cap identification remain
internal construction duties: this adapter does not add either as a third
external assumption to the final core theorem. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunQLocalAdmission
open Filter Lattice RG FullQLocal PhysicalNext.Repeat.Legato
open ActualRunAdmissionScales ActualRunComponentAdmission
open scoped Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]

/-- The original Run's retained readout purchase supplies precisely the
preMesh premise used in the numerical proof. -/
theorem actual_preMesh (R : Run G) (h : RG05Preconstruction.ReadoutPurchase R.b) :
    ActualRunAdmissionClock.PreMesh R.family.path.levels := by
  intro m
  change ((R.alloy.B.a.S.block m).val : ℝ) ≤
    1+Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta m))
  exact h.preMesh m

/-- The component width is below both original stored profile widths.
This upper comparison deliberately does not claim reciprocal payment. -/
theorem pair_le_original (R : Run G) (W : ProfileWidths)
    (hW : ∀ i, W.width i ≤ (R.metals.p.profile i).width) (m : ℕ) :
    W.pair R.family m ≤ pairWidth R.family.path.levels m := by
  change min (W.width (R.family.path.levels.clock.J (m+1)))
    (W.width (R.family.path.levels.clock.J m)) ≤
    min (R.family.path.levels.params (m+1)).width (R.family.path.levels.params m).width
  rw [ActualRunQlocalWidths.stored_width R (m+1), ActualRunQlocalWidths.stored_width R m]
  exact min_le_min (hW _) (hW _)

/-- Internal assembly: all costs and tails are proved here; the exact
selected-width purchase and selected-output calibration cap must be provided
by their original same-Run construction, not assumed in the final theorem. -/
def ofPayment (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (hMesh : ActualRunAdmissionClock.PreMesh C.path.levels)
    (W : ProfileWidths) (P : WidthPayment C W) (J : LocalComparison.Global.Setup V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m) (hcap0 : Tendsto cap atTop (𝓝 0)) :
    LocalComparison.Global.Admission C (onFamily J W C) where
  inputNorm m := requestedBudget C.path.levels (m+1) J.inputFieldOrder
    J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve)
    (J.output_support_pos.trans J.support_reserve)
  outputNorm m := requestedBudget C.path.levels m J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum J.output_support_pos
  input_norm m := requested_norm C (m+1) J.inputFieldOrder
    J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve)
    (J.output_support_pos.trans J.support_reserve)
  output_norm m := requested_norm C m J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum J.output_support_pos
  inputWidth := W.pair C
  outputWidth m := W.pair C m/2
  input_width_pos := W.pair_positive C
  output_width_pos m := div_pos (W.pair_positive C m) (by norm_num)
  width_reserve m := by have hp := W.pair_positive C m; linarith
  input_width_eq := rfl
  output_width_eq := rfl
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
    rw [min_eq_right (show W.pair C m/2 ≤ W.pair C m by linarith)]
    exact rate_width C W m
  path_rate_cost := rate_cost C W
  regular_flat a c t := eventually_atTop.1
    (ActualRunComponentAdmission.regular_flat C W P hG hC hMesh a c t)
  forced_flat δ hδ a c d t := eventually_atTop.1
    (ActualRunComponentAdmission.forced_flat C W P hG hC hMesh δ hδ a c d t)

/-- The same Run and its original readout purchase instantiate the complete
numerical record. No replacement trajectory or new geometric premise is used. -/
def atRun (R : Run G) (hG : G.Simple) (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (W : ProfileWidths) (P : WidthPayment R.family W) (J : LocalComparison.Global.Setup V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m) (hcap0 : Tendsto cap atTop (𝓝 0)) :
    LocalComparison.Global.Admission R.family (onFamily J W R.family) :=
  ofPayment R.family hG R.makes (actual_preMesh R hReadout) W P J cap hcap hcap0

end YM.Integration.ActualRunQLocalAdmission
end
