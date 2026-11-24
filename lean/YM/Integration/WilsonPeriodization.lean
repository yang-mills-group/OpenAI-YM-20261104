import YM.Integration.WilsonIRSource
import YM.Integration.PeriodicCoefficientMass

/-! Exact cover-to-torus identity and coefficient-price control for the same
restored Wilson insertion. Wrapping is allowed to identify cover variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson PowerSeries RG06 RG06.WilsonCompiler
open scoped BigOperators Classical
variable {G : Gauge} {n : Side}

def coverAddress (x : Site n) : LinkVar G ℤ → LinkVar G (Per n) :=
  fun i => ((wrap n i.1.1 + x, i.1.2), i.2)

theorem develop_rename {V W : Type*} (f : V → W) (a : W → ℝ)
    (P : PowerSeries (Pigment V)) :
    develop a (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
      develop (a ∘ f) P := by
  ext1 k
  simp only [develop_coeff, PowerSeries.coeff_map]
  exact MvPolynomial.eval_rename _ _ _

theorem markSite_periodize (C : Family G) (d : ℕ) (v : C.label d)
    (x : Site n) :
    markSite C d v x = PowerSeries.map
      (MvPolynomial.rename (coverAddress (G := G) x)).toRingHom (markTop C d v) := by
  apply folio_ext
  intro a
  rw [develop_rename]
  have ha : access G (expandAt x (peeling G a)) = a ∘ coverAddress x := rfl
  simpa only [access_peel, ha] using
    (site_wrapped x (peeling G a) C v).symm

variable (C : Family G) (N p d : ℕ)
    (x : Site (C.side N p)) (v : C.label d)

def physicalCoverFilm : PowerSeries (Pigment (LinkVar G ℤ)) :=
  PowerSeries.C (MvPolynomial.C (Dict06.Actual.factor C N d)) *
    markTop C d (Dict06.Actual.matrix C N p d v)

theorem physicalFilm_periodize :
    physicalFilm C N p d x v = PowerSeries.map
      (MvPolynomial.rename (coverAddress (G := G) x)).toRingHom
        (physicalCoverFilm C N p d v) := by
  rw [physicalFilm, physicalCoverFilm, map_mul, PowerSeries.map_C,
    markSite_periodize]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_C]

/-- Exact cover price, including the actual calibration and engineering
factor. No injectivity of the periodization map or large-period hypothesis. -/
theorem physicalFilm_periodic_mass (k : ℕ)
    (w : (LinkVar G (Per (C.side N p)) →₀ ℕ) → ℝ) (hw : ∀ m, 0 ≤ w m) :
    (∑ m ∈ (PowerSeries.coeff k (physicalFilm C N p d x v)).support,
      w m * ‖MvPolynomial.coeff m (PowerSeries.coeff k (physicalFilm C N p d x v))‖) ≤
    ∑ m ∈ (PowerSeries.coeff k (physicalCoverFilm C N p d v)).support,
      w (m.mapDomain (coverAddress x)) *
        ‖MvPolynomial.coeff m (PowerSeries.coeff k (physicalCoverFilm C N p d v))‖ := by
  rw [physicalFilm_periodize, PowerSeries.coeff_map]
  exact rename_weighted_mass_le (coverAddress x) _ w hw

theorem wilsonIRSource_cover_mass (hC : C.Makes)
    (i : (C.labels.level d).Index) (k : ℕ)
    (w : (RG09.Graph.Tor (RG09.Walls.Spin G) (C.side N p) →₀ ℕ) → ℝ)
    (hw : ∀ m, 0 ≤ w m) :
    let v := Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)
    (∑ m ∈ (wilsonIRSource C N p d x i k).support,
      w m * |MvPolynomial.coeff m (wilsonIRSource C N p d x i k)|) ≤
    ∑ m ∈ (PowerSeries.coeff k (physicalCoverFilm C N p d v)).support,
      w ((m.mapDomain (coverAddress x)).mapDomain (RG09.Walls.assign G)) *
        ‖MvPolynomial.coeff m (PowerSeries.coeff k (physicalCoverFilm C N p d v))‖ := by
  intro v
  rw [wilsonIRSource_weighted_mass C N p d x i hC k]
  exact physicalFilm_periodic_mass C N p d x v k _ (fun m => hw _)

end YM.Integration
