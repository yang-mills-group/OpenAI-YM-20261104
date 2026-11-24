import YM.Integration.WilsonMaxwellThermometerKineticCoordinate
import YM.Integration.WilsonPositionRawCutoff
import YM.Integration.WilsonPositionRawDetector

/-! Oriented first slope on the actual unshifted, seven-face original thermometer.
The common internal kinetic variable need not settle at fixed physical radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticSlope
open Set Filter Function Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register Lattice Wilson RG Source Extraction Table Spec PhysMS RG17 Trace.Pilot
open Climb PhysicalNext.Repeat.Legato
open WilsonMaxwellThermometerKineticCoordinate
open scoped BigOperators Topology Classical
variable {G : Gauge} (Z : WilsonPrescription G)

theorem slope (m : Mesh) (u : ℝ) :
    printed Z m 1 u = ground Z m +
      Rose.c_T Z.criterion * WilsonPositionRawDetector.linear Z m * u := by
  have h := Rose.puts Z.scheme Z.criterion m 1 (by decide)
  have se := congrArg Complex.re h
  rw [←Complex.ofReal_inv, Complex.re_ofReal_mul] at se
  have hn : Rose.c_T Z.criterion ≠ 0 := Z.criterion.fresh.ne
  change (∑ j : Fin 2, (PowerSeries.coeff j (Rose.Detector Z.scheme Z.criterion m)).re * u^(j:ℕ)) = _
  rw [Fin.sum_univ_two]
  simp [ground, WilsonPositionRawDetector.linear, se, hn]

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S)
    (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
local notation "out" => WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A
local notation "thermal" => WilsonPositionRawCutoff.thermometer Z F J A

theorem exact_report (m : Mesh) (r : ℝ) (z : ℕ × ℕ) {u : ℝ} (hu : u ≠ 0) :
    thermal r z / u =
      (((out r z).re - printed Z m 1 u) / u + ground Z m / u) / Rose.c_T Z.criterion +
        WilsonPositionRawDetector.linear Z m := by
  change (out r z).re / Rose.c_T Z.criterion / u = _
  rw [slope]
  field_simp [hu,Z.criterion.fresh.ne]
  ring

/-- The independently oriented first coefficient is restored only after charging the
finite ground and the true seven-face error on the one ordered extraction. -/
theorem ordered {Y : Ultrafilter (ℕ×ℕ)} (simple : G.Simple)
    (mesh : ℝ×(ℕ×ℕ) → Mesh) (axis : ℝ×(ℕ×ℕ) → ℝ)
    (cofinal : Tendsto mesh (trail.curry (Y : Filter _)) Front)
    (positive : ∀ᶠ w in trail.curry (Y : Filter _), 0 < axis w)
    (joint : Tendsto (fun w => ((out w.1 w.2).re - printed Z (mesh w) 1 (axis w)) / axis w)
        (trail.curry (Y : Filter _)) (𝓝 0))
    (constant : Tendsto (fun w => ground Z (mesh w) / axis w)
        (trail.curry (Y : Filter _)) (𝓝 0)) :
    Tendsto (fun w => thermal w.1 w.2 / axis w) (trail.curry (Y : Filter _)) (𝓝 1) := by
  have hz := ((Rose.xc Z.scheme Z.criterion simple).comp cofinal)
  have hs : Tendsto (fun w => WilsonPositionRawDetector.linear Z (mesh w))
      (trail.curry (Y : Filter _)) (𝓝 1) := Complex.continuous_re.continuousAt.tendsto.comp hz
  have total := ((joint.add constant).div_const (Rose.c_T Z.criterion)).add hs
  simp only [zero_add, zero_div] at total
  refine total.congr' ?_
  filter_upwards [positive] with w hw
  exact (exact_report Z F J A (mesh w) w.1 w.2 hw.ne').symm

end YM.Integration.WilsonMaxwellThermometerKineticSlope
