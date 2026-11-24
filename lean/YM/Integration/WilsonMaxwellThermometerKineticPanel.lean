import YM.Integration.WilsonMaxwellThermometerKineticSlope
import YM.Integration.WilsonPositionFineDetectorSource
import YM.Integration.WilsonMaxwellThermometerFirstRemainder

/-! Both scalar comparisons use the same full seven ordinary faces, with the signed
constant and all occupied first coefficients retained through the position change. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticPanel
open Filter Set Function Finset PowerSeries Maxwell XSpace XSpace.Retirement XSpace.Structure1
open XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register Lattice Wilson RG Source Extraction Table Spec
open Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open WilsonMaxwellThermometerKineticCoordinate
open scoped BigOperators Topology Classical
variable {G : Gauge} (Z : WilsonPrescription G)

abbrev Board := Points 3 → Rose.Badge → PowerSeries ℂ

/-- The original test is applied to the whole connected polynomial of its joint board. -/
def sampled (E : Board) (q : ℕ) (u : ℝ) : ℝ :=
  ((Rose.test Z.criterion).applyTo fun x => ∑ j : Fin (q+1),
    coeff j (Rose.b3 (E x)) * (u:ℂ)^(j:ℕ)).re

theorem filed (m : Mesh) (q : ℕ) (u : ℝ) :
    printed Z m q u = WilsonPositionFineDetectorSource.faces Z m q u := by
  unfold printed WilsonPositionFineDetectorSource.faces
  exact sum_congr rfl fun j _ => by rw [Rose.detector]; rfl

theorem paid_ground (m : Mesh) (bought : Z.store.Meets Z.scheme m 6) : ground Z m = 0 := by
  have h := congrArg (coeff 0) (Rose.prepared_odd Z.scheme Z.criterion m bought)
  rw [Rose.inversion,coeff_rescale,map_neg,pow_zero,one_mul] at h
  change coeff 0 (Rose.Detector Z.scheme Z.criterion m) = -coeff 0 _ at h
  have z : coeff 0 (Rose.Detector Z.scheme Z.criterion m)=0 := by linear_combination h/2
  rw [ground,z]; rfl

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S)
    (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
    {Y : Ultrafilter (ℕ×ℕ)}
local notation "visits" => trail.curry (Y : Filter (ℕ × ℕ))
local notation "out" => WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A
local notation "thermal" => WilsonPositionRawCutoff.thermometer Z F J A
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

theorem hearing (simple : G.Simple) (mesh : ℝ×(ℕ×ℕ) → Mesh)
    (axis : ℝ×(ℕ×ℕ) → ℝ) (E : ℝ×(ℕ×ℕ) → Board)
    (cofinal : Tendsto mesh visits Front) (pos : ∀ᶠ w in visits, 0 < axis w)
    (joint : Tendsto (fun w => ((out w.1 w.2).re - sampled Z (E w) 1 (axis w)) / axis w)
      visits (𝓝 0))
    (change : Tendsto (fun w => (sampled Z (E w) 1 (axis w) -
      WilsonPositionFineDetectorSource.faces Z (mesh w) 1 (axis w)) / axis w) visits (𝓝 0)) :
    Tendsto (fun w => thermal w.1 w.2 / axis w) visits (𝓝 1) := by
  apply WilsonMaxwellThermometerKineticSlope.ordered Z F J A simple mesh axis cofinal pos
  · have total := joint.add change
    rw [zero_add] at total
    exact total.congr fun w => by rw [filed]; ring
  · have issued := cofinal.eventually (Z.store.nested_solution Z.scheme 6 Cirrus.frontier).2
    apply tendsto_congr' _ |>.mpr (tendsto_const_nhds (x:=(0:ℝ)))
    filter_upwards [issued] with w hw
    simp [paid_ground Z (mesh w) hw.1]

end YM.Integration.WilsonMaxwellThermometerKineticPanel
