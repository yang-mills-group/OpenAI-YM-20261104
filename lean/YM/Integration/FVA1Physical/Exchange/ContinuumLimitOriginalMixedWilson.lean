import Mathlib.RingTheory.PowerSeries.Inverse
import YM.CommonCover.JetCumulants
import YM.Comparison.RG02.Bulk.Fk

/-! Mixed complex insertions for the original finite Gaussian Wilson prescription.
The denominator is the zero-mark row of the independently integrated full
action. Each incoming hot log mode has its own source germ, including
nonsingleton modes. All finite Taylor truncations use the same integral table. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.OriginalMixedWilson

open Function Finset MeasureTheory RG Wilson Gauge Precision Tree Lattice
open Exterior Input PertExtension.Series Next.SectorChange PowerSeries
open Comparison.RG02 Order Assembly Marker Multi
open CommonCover.JetCumulants
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
    {P : PathData G} {O : ChartRatio G} {I : Type} [DecidableEq I] [Fintype I]
    {R : Census I} (K : Bulk.Kernel S p P O) (F : Forest S.ratio)
    (ρ : S.Choices) (W : Bulk.Colors R G f) (x : fieldDir G c 1)

local notation "Noise" => Precision.Key F G → ℝ
local notation "PS" => PowerSeries ℂ
local notation "originAt" => Bulk.translated K F x

/-- Original incoming log jets for every hot subset, evaluated at the
stationary lifted coarse field plus the common integration variable. -/
def logInputs (v : Noise) (s : R.Mode) : PS :=
  if hs : s.val.Nonempty then
    PowerSeries.mk (fun j => markLetter W.power (Bulk.markFn S F W) ⟨s, hs⟩ (originAt v) j)
  else 0

/-- Wick action weight before any marker normalization. The field-independent
Haar and action data belong to the same `Bulk.geometric` as the Wilson kernel. -/
def quietWeight (v : Noise) : PS :=
  PowerSeries.map Complex.ofRealHom (PowerSeries.mk fun j =>
    Radial.expsum (Radial.layers (Bulk.geometric K F ρ W)) j j (originAt v))

def mixedWeight (v : Noise) (s : R.Mode) : PS :=
  quietWeight K F ρ W x v * expTable R (logInputs K F W x v) s

/-- Integrate all grades at the shared forest, covariance, coarse field and
geometry. This separately defined function is independent of the output order. -/
def raw (s : R.Mode) : PS :=
  PowerSeries.mk fun j => ∫ v : Noise, coeff j (mixedWeight K F ρ W x v s)
    ∂Gaussian.cloud (K.covariance F ρ)

private theorem logInputs_curve (v : Noise) :
    curve W.power (Bulk.markFn S F W) (originAt v) = depot R (logInputs K F W x v) := by
  ext1 j
  ext s
  rw [depot_known]
  by_cases hs : s.val.Nonempty
  · rw [curve, coeff_mk]
    exact (part_lit _ (⟨s, hs⟩ : Hot R)).trans (by rw [logInputs, dif_pos hs, coeff_mk])
  · have hq : s = R.quiet := by
      by_contra h
      exact hs ((Cumulants.hot_iff_ne s).2 h)
    subst s
    rw [mark_curve_quiet, logInputs, dif_neg hs, map_zero]

private theorem expanded (v : Noise) :
    expansions W.power (Bulk.markFn S F W) (Bulk.geometric K F ρ W) (originAt v) =
      depot R (mixedWeight K F ρ W x v) := by
  have h : realCurve R (fun j => Radial.expsum (Radial.layers (Bulk.geometric K F ρ W)) j j
        (originAt v)) = ship R (quietWeight K F ρ W x v) := by
    ext1 j
    rw [realCoeff, ship, quietWeight, coeff_map, coeff_map, coeff_mk]
    rfl
  unfold mixedWeight expansions
  rw [h, logInputs_curve, ←depot_positive, ←depot_scale]

private theorem row (j : ℕ) (s : R.Mode) (v : Noise) :
    insideMoment (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W)
        (Bulk.geometric K F ρ W) s j v = coeff j (mixedWeight K F ρ W x v s) := by
  change (coeff j (expansions _ _ _ (originAt v))).part s = _
  rw [expanded, depot_known]

/-- All coefficient integrals in the independently specified table exist as
absolutely integrable complex moments on the native covariance. -/
theorem integrable_moment (j : ℕ) (s : R.Mode) :
    Integrable (fun v : Noise => coeff j (mixedWeight K F ρ W x v s))
      (Gaussian.cloud (K.covariance F ρ)) := by
  have h := (gather (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W)
    (Bulk.geometric K F ρ W) (K.covariance F ρ) (K.symm F ρ)
    (K.positive F ρ) s (pick j j)).1
  rw [picked j le_rfl] at h
  exact h.congr (Filter.Eventually.of_forall (row K F ρ W x j s))

/-- Physical Wick recursion versus all joint complex moment rows. -/
theorem gaussian_table (r : ℕ) :
    Bulk.Fk K F ρ W x r = Order.series R r (depot R (raw K F ρ W x)) := by
  apply (Order.sym_coeff _ _ (Bulk.fk_sym ..) (Order.Symmetric.known _)).mpr
  intro j hj
  ext s
  rw [observation _ _ _ hj, depot_known, raw, coeff_mk]
  have h := order_read (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W)
      (Bulk.geometric K F ρ W) (K.covariance F ρ) (K.symm F ρ) (K.positive F ρ) s hj
  exact h.trans (integral_congr_ae (Filter.Eventually.of_forall (row K F ρ W x j s)))

/-- The physical quiet integral has unit constant term by the original
leading Gaussian rule. No choice of external normalizing series is required. -/
theorem quiet_constant : constantCoeff (raw K F ρ W x R.quiet) = 1 := by
  have h := Bulk.fk_unit K F ρ W x 0
  rw [gaussian_table] at h
  unfold UnitLeading at h
  rw [←Join.pair_quiet, polarization] at h
  change ((0 : ℕ).factorial : ℂ) * (coeff 0 (depot R (raw K F ρ W x))).part R.quiet = 1 at h
  rw [depot_known] at h
  simpa only [Nat.factorial_zero, Nat.cast_one, one_mul, coeff_zero_eq_constantCoeff_apply] using h

def vacuum : (PS)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr
    (show IsUnit (constantCoeff (raw K F ρ W x R.quiet)) from by rw [quiet_constant]; exact isUnit_one)).unit

theorem vacuum_value : (vacuum K F ρ W x : PS) = raw K F ρ W x R.quiet :=
  IsUnit.unit_spec _

def normalized (s : R.Mode) : PS :=
  (↑((vacuum K F ρ W x)⁻¹) : PS) * raw K F ρ W x s

theorem normalized_quiet : normalized K F ρ W x R.quiet = 1 := by
  rw [normalized, ←vacuum_value, Units.inv_mul]

theorem multiply_back (s : R.Mode) :
    raw K F ρ W x R.quiet * normalized K F ρ W x s = raw K F ρ W x s := by
  rw [normalized, ←vacuum_value, ←mul_assoc, Units.mul_inv, one_mul]

private theorem denominator_series (r : ℕ) :
    denominator (Bulk.Fk K F ρ W x r) = series R r (ship R (raw K F ρ W x R.quiet)) := by
  rw [gaussian_table]
  unfold denominator
  rw [bottom_map]
  apply congrArg _
  ext1 j
  ext t
  rw [ship, coeff_map, coeff_map, pure_marks, depot_known, beads]

/-- Every finite graded Wilson log row is given by the same absolutely
integrated all-mode table divided by its own physical vacuum. -/
theorem connected_coefficients (r j : ℕ) (hj : j ≤ r) (s : R.Mode) :
    (observe R r (logMarked (Bulk.Fk K F ρ W x r)) j).part s =
      coeff j (logTable R (normalized K F ρ W x) s) := by
  let z := raw K F ρ W x R.quiet
  let u := normalized K F ρ W x
  have h : depot R (raw K F ρ W x) = ship R z * depot R u := by
    rw [←depot_scale]
    exact congrArg (depot R) (funext (fun t => (multiply_back K F ρ W x t).symm))
  have he : series R r (depot R u) = ratio (Bulk.Fk K F ρ W x r) := by
    apply ratio_unique (Bulk.fk_unit ..)
    rw [denominator_series]
    change series R r (ship R z) * series R r (depot R u) = _
    rw [←map_mul, ←h, ←gaussian_table]
  rw [logMarked, ←he, depot_connected u (normalized_quiet ..), observation _ _ _ hj, depot_known]

/-- Finite set partitions now give the *individually normalized* connected
Wilson coefficients for arbitrary mixed log inputs, including complex data. -/
theorem partition_coefficients (r j : ℕ) (hj : j ≤ r) (s : R.Mode) :
    (observe R r (logMarked (Bulk.Fk K F ρ W x r)) j).part s =
      coeff j (∑ a ∈ Multi.shards R s, Cumulants.mobiusTop a.val.card •
        ∏ i ∈ a.val, normalized K F ρ W x i.val) := by
  rw [connected_coefficients K F ρ W x r j hj s,
    mass_log R (normalized K F ρ W x) s (normalized_quiet K F ρ W x)]

end YM.Integration.FVA1Physical.OriginalMixedWilson
