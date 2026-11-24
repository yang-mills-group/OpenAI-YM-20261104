import YM.Integration.WilsonIRSource

/-! Pass the actual real IR source through the existing tagged-product
compiler. This keeps its collision rule, the actual calibrated basis labels,
the common reset variable, and the ordinary factorial convention. Products
are identified before Wick contraction or division by a vacuum series. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson PowerSeries RG06 RG06.WilsonCompiler
open scoped BigOperators Classical

variable {G : Gauge} (C : Family G) (N p d : ℕ)
    (x : Site (C.side N p)) (i : (C.labels.level d).Index)
    (a : RG09.Graph.Tor (RG09.Walls.Spin G) (C.side N p) → ℝ)

def wilsonIRSeries : PowerSeries ℂ :=
  PowerSeries.mk (fun k => (MvPolynomial.eval a (wilsonIRSource C N p d x i k) : ℂ))

theorem wilsonIRSeries_develop (hC : C.Makes) :
    wilsonIRSeries C N p d x i a =
      develop (a ∘ RG09.Walls.assign G)
        (physicalFilm C N p d x
          (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) := by
  ext1 k
  rw [wilsonIRSeries, PowerSeries.coeff_mk, develop_coeff,
    wilsonIRSource_eval C N p d x i hC k a]
  simpa only [access_peel] using
    (physicalFilm_coefficient C N p d x
      (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))
      (peeling G (a ∘ RG09.Walls.assign G)) k).symm

variable {V I : Type*} [DecidableEq V] (R : Marker.Census V)
    (tag : I → R.Mode) (degree : I → ℕ)
    (positions : I → Site (C.side N p))
    (basis : (j : I) → (C.labels.level (degree j)).Index)

/-- Arbitrarily many actual marked insertions use the real IR source series
with the existing tag algebra, including repeated or colliding tags. -/
theorem wilsonIRSeries_tagged_product (hC : C.Makes) (s : Finset I) (q : R.Mode) :
    Dict06.Series.ps (fun t =>
      (Dict06.Actual.many C N p R tag degree positions
        (fun j => Dict06.Actual.calibrate C N p (degree j)
          ((C.labels.level (degree j)).basis (basis j))) s
        (Dict06.Wil.positive (peeling G (a ∘ RG09.Walls.assign G)) t)).part q) =
    PowerSeries.mk (fun k =>
      (PowerSeries.coeff k (Dict06.Tags.occurrences R tag
        (fun j => wilsonIRSeries C N p (degree j) (positions j) (basis j) a) s)).part q) := by
  simp_rw [wilsonIRSeries_develop C N p _ _ _ a hC]
  simpa only [access_peel] using
    physicalFilm_tagged_product C N p R tag degree positions
      (fun j => Dict06.Actual.calibrate C N p (degree j)
        ((C.labels.level (degree j)).basis (basis j)))
      (peeling G (a ∘ RG09.Walls.assign G)) s q

end YM.Integration
