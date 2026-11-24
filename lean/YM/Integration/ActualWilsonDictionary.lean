import YM.Dict06.Actual.Insertion
import YM.RG06.Wilson.Motif

/-! Identify two independently supplied coefficient dictionaries on the same
actual cutoff insertion before products or Wick contraction. The finite IR
inversion-quotient prescription and its schedule estimates remain separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson PowerSeries
open RG06 RG06.WilsonCompiler
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (C : Family G) (N p d : ℕ)

/-- The exact restored cutoff insertion, in RG06's positive-link variables.
The terminal inverse, threshold scaling and engineering factor are retained. -/
def physicalFilm (x : Site (C.side N p)) (v : C.label d) :
    PowerSeries (Pigment (LinkVar G (Per (C.side N p)))) :=
  PowerSeries.C (MvPolynomial.C (Dict06.Actual.factor C N d)) *
    markSite C d (Dict06.Actual.matrix C N p d v) x

theorem physicalFilm_garnish (x : Site (C.side N p)) (v : C.label d)
    (A : Links (Per (C.side N p)) G.Color) :
    GSeries.Garnish 0 (fun t => C.O N p v x (roll A t))
      (develop (access G A) (physicalFilm C N p d x v)) := by
  rw [physicalFilm, map_mul, quoted]
  exact GSeries.Garnish.C_mul (Dict06.Actual.factor C N d)
    (orbit C d (Dict06.Actual.matrix C N p d v) x A)

/-- Both suppliers use ordinary derivatives divided by factorials, at zero. -/
theorem dictionary_series_convention (f : ℝ → ℂ) :
    Dict06.Series.ps f = GSeries.assembler 0 f := rfl

/-- Equality with the actual single-insertion supplier is proved, rather than
assumed as an emission/source compatibility premise. -/
theorem physicalFilm_auth (x : Site (C.side N p)) (v : C.label d)
    (A : Links (Per (C.side N p)) G.Color) :
    develop (access G A) (physicalFilm C N p d x v) =
      Dict06.Actual.auth C N p d x v A := by
  calc
    _ = GSeries.assembler 0 (fun t => C.O N p v x (roll A t)) :=
      (physicalFilm_garnish C N p d x v A).series
    _ = Dict06.Series.ps (fun t => C.O N p v x (Dict06.Wil.positive A t)) := rfl
    _ = _ := (Dict06.Actual.honest C N p d x v A).2

/-- Exact coefficient identification in the common reset variable. -/
theorem physicalFilm_coefficient (x : Site (C.side N p)) (v : C.label d)
    (A : Links (Per (C.side N p)) G.Color) (k : ℕ) :
    tone (access G A) (PowerSeries.coeff k (physicalFilm C N p d x v)) =
      Dict06.Series.ordinary k (fun t => C.O N p v x (roll A t)) := by
  exact (develop_coeff _ _ _).symm.trans
    ((physicalFilm_garnish C N p d x v A).coeff k)

/-- Applying and undoing the existing physical label calibration gives the
unscaled input film, with only its prescribed engineering factor. -/
theorem physicalFilm_calibrated (x : Site (C.side N p)) (v : Labels.Label G d) :
    physicalFilm C N p d x (Dict06.Actual.calibrate C N p d v) =
      PowerSeries.C (MvPolynomial.C (Dict06.Actual.factor C N d)) *
        markSite C d ((C.labels.level d).coords v) x := by
  unfold physicalFilm
  rw [Dict06.Actual.meet]

variable {V I : Type*} [DecidableEq V] (R : Marker.Census V)
    (tag : I → R.Mode) (degree : I → ℕ)
    (x : I → Site (C.side N p)) (v : (i : I) → C.label (degree i))

/-- The same dictionary identity passes through the existing tagged-product
compiler, including its collision rule; no new product or Wick convention. -/
theorem physicalFilm_tagged_product
    (A : Links (Per (C.side N p)) G.Color) (s : Finset I) (q : R.Mode) :
    Dict06.Series.ps (fun t =>
      (Dict06.Actual.many C N p R tag degree x v s (Dict06.Wil.positive A t)).part q) =
    PowerSeries.mk (fun k =>
      (PowerSeries.coeff k (Dict06.Tags.occurrences R tag
        (fun i => develop (access G A) (physicalFilm C N p (degree i) (x i) (v i))) s)).part q) := by
  simp_rw [physicalFilm_auth]
  exact Dict06.Actual.read_all C N p R tag degree x v A s q

end YM.Integration
