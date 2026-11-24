import YM.Integration.WilsonMovingTaylorConvention
import YM.Integration.WilsonBookedSectionGerm
import YM.RGComparison.Core16.Spool.Beacon

/-! The actual funded Wilson lamp at every translated UV site. It has the
same Taylor series as the independently prescribed formal section after the
true engineering power and tested coefficient have been restored. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingSectionLamp
open Function Lattice Exterior Wilson Stationary Precision RG Push.Uniform Bloch
open PhysicalNext.Repeat.Legato RGComparison.Core16.Spool
open FormalBulk08 Jets Reef Mesa Flat Pose Kemp Rial Lotus Planned.PrimaryIntegral295
open Place
open Shore Gorge City Cork Rift Lava Glide Bank Dawn Wine Roof Dove
open scoped Classical ContDiff PowerSeries

def place (G : Gauge) {n : Side} (o : Site n) : wire G n → Primary n G :=
  (WilsonMovingGaussianCoordinates.link G n).symm ∘ Lotus.tint o

theorem translate (G : Gauge) {n : Side} (o : Site n) (x : Jets.Rays (Primary n G)) :
    Stationary.input G n (x ∘ place G o) =
      Lattice.translate o (represent ((tint G (Body 1 n)) x)) := rfl

theorem resited (G : Gauge) {n : Side} (o : Site n) (t : PowerSeries (MvPolynomial (wire G n) ℝ)) :
    PowerSeries.map (MvPolynomial.rename (WilsonMovingGaussianCoordinates.link G n).symm).toRingHom
      (Kemp.resite o t) = PowerSeries.map (MvPolynomial.rename (place G o)).toRingHom t := by
  apply PowerSeries.ext
  intro j
  simp only [Kemp.resite, PowerSeries.coeff_map, place]
  exact MvPolynomial.rename_rename ..

/-- At an arbitrary site on the actual issued period, including every
fine-cell preimage. The right side is a real physical group-field reading
before taking Taylor coefficients, with the genuine section valuation. -/
theorem ultraviolet {G : Gauge} (R : Run G) {d D : ℕ}
    (L : ∀ i, Lodge ((R.alloy.B.a.clock.op i 0).patch)) (a : hue G) (depth : d < D)
    (N per : ℕ) (b : Letter (R.family.labels.level d)) (f : Dawn.Studio D)
    (k : ℕ) (bound : ((R.family.labels.level d).grades (mint _ b)).2 ≤ k)
    (o : Site (R.family.side N per)) :
    let F := R.family.labels.level d
    let n := R.family.side N per
    let w := Dawn.notch (pet F b) ((Dawn.paper_fits (pet F b)).trans (Nat.le_trans d.le_succ depth)) f
    let lamp := investment (R.makes.sections d) (CoefficientBridge.run_valuation R d) (mint F b)
    PowerSeries.map (MvPolynomial.rename (place G o)).toRingHom
      (PowerSeries.X ^ (F.grades (mint F b)).2 *
        Kemp.banner k (WilsonRunFormalMarkedStep.graph R L a depth N N b f) n) =
      PowerSeries.C (MvPolynomial.C w) * paste (fun x : Jets.Rays (Primary n G) =>
        (Light lamp n o (represent ((tint G (Body 1 n)) x))).re) := by
  intro F n w lamp
  let T := R.family.localSection d
  let read := fun x : Jets.Rays (wire G n) =>
    (T.places (copy F (mint F b)) 0 (Stationary.input G n x)).re
  have smooth : ContDiffAt ℝ ∞ read 0 := Rial.coatG T n (mint F b)
  have p := WilsonMovingTaylorConvention.placed (place G o) read smooth
  have field : (fun x : Jets.Rays (Primary n G) => read (x ∘ place G o)) =
      fun x => (Light lamp n o (represent ((tint G (Body 1 n)) x))).re := by
    funext x
    change (T.places (copy F (mint F b)) 0 (Stationary.input G n (x ∘ place G o))).re = _
    rw [translate, Source.SectionData.places_trans, zero_add]
    rfl
  rw [WilsonBookedSectionGerm.ultraviolet R L a depth N per b f k bound, map_mul]
  change PowerSeries.map _ (PowerSeries.C (MvPolynomial.C w)) *
    PowerSeries.map _ (paste read) = _
  rw [p, field]
  simp

end YM.Integration.WilsonMovingSectionLamp
end
