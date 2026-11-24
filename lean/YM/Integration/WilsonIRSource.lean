import YM.Integration.ActualWilsonDictionary
import YM.Integration.RealCoefficientProjection
import YM.RG06.Wilson.Banner

/-! The actual calibrated Wilson basis insertion as a real polynomial in
RG09's existing torus variables. This identifies the one-insertion source
before products and Wick contraction. It does not construct a Scout.Cinema
or assert inversion-quotient equality or structural schedule estimates. -/
set_option autoImplicit false
noncomputable section
/- The finite Wilson insertions use the five coordinate declarations below. -/
namespace RG09.Graph
open YM YM.Lattice
abbrev Leg (T X:Type*) := T × X
abbrev Tor (T:Type*) (n:Side):= Leg T (Site n)
end RG09.Graph

namespace RG09.Wick
abbrev polys(T:Type*) := MvPolynomial T ℝ
end RG09.Wick

namespace RG09.Walls
open YM YM.Lattice RG09.Graph
variable {n : Side} (G : Gauge)
abbrev Spin(G:Gauge):= Axis × G.ColorIndex
def assign : Edge (Site n) × G.ColorIndex ≃ Tor (Spin G) n where
   toFun i:=((i.1.2,i.2),i.1.1)
   invFun i:=((i.2,i.1.1),i.1.2)
   right_inv _i:=rfl
   left_inv _i:=rfl
end RG09.Walls

namespace YM.Integration
open Lattice Wilson PowerSeries RG06 RG06.WilsonCompiler
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} (C : Family G) (N p d : ℕ)
    (x : Site (C.side N p)) (i : (C.labels.level d).Index)

set_option quotPrecheck false in
local notation "label" => Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)
local notation "film" => physicalFilm C N p d x label

theorem physicalFilm_basis_conjugate (hC : C.Makes) :
    PowerSeries.map (conjugateP (LinkVar G (Per (C.side N p)))) film = film := by
  rw [physicalFilm_calibrated, (C.labels.level d).coords_basis, map_mul,
    PowerSeries.map_C, ← site_star C hC]
  have hi : star (Pi.single i (1 : ℂ) : C.label d) = Pi.single i 1 := by
    funext j
    simp only [Pi.star_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hi]
  congr 1
  unfold conjugateP
  rw [MvPolynomial.map_C]
  congr 1
  simp [Dict06.Actual.factor]

theorem physicalFilm_basis_coeff_conjugate (hC : C.Makes) (k : ℕ) :
    MvPolynomial.map (starRingEnd ℂ) (PowerSeries.coeff k film) =
      PowerSeries.coeff k film := by
  have h := congrArg (PowerSeries.coeff k)
    (physicalFilm_basis_conjugate C N p d x i hC)
  simpa only [PowerSeries.coeff_map, conjugateP] using h

/-- Use the consumer's existing `Walls.assign`, including its exact edge,
axis and color coordinates; no guessed source-variable identification. -/
def wilsonIRSource (k : ℕ) :
    RG09.Wick.polys (RG09.Graph.Tor (RG09.Walls.Spin G) (C.side N p)) :=
  MvPolynomial.rename (RG09.Walls.assign G)
    (realPolynomial (PowerSeries.coeff k film))

/-- Exact source equality for the actual physical insertion at every real
torus field. The reset variable and its ordinary factorial convention agree. -/
theorem wilsonIRSource_eval (hC : C.Makes) (k : ℕ)
    (a : RG09.Graph.Tor (RG09.Walls.Spin G) (C.side N p) → ℝ) :
    (MvPolynomial.eval a (wilsonIRSource C N p d x i k) : ℂ) =
      Dict06.Series.ordinary k (fun t => C.O N p label x
        (roll (peeling G (a ∘ RG09.Walls.assign G)) t)) := by
  rw [wilsonIRSource, MvPolynomial.eval_rename]
  rw [← realPolynomial_eval (physicalFilm_basis_coeff_conjugate C N p d x i hC k)]
  simpa only [access_peel, tone] using
    physicalFilm_coefficient C N p d x label
      (peeling G (a ∘ RG09.Walls.assign G)) k

/-- All coefficient-weighted structural prices pass to the real IR source
without loss. This equality does not provide the RG08 schedule's prices. -/
theorem wilsonIRSource_weighted_mass (hC : C.Makes) (k : ℕ)
    (w : (RG09.Graph.Tor (RG09.Walls.Spin G) (C.side N p) →₀ ℕ) → ℝ) :
    (∑ m ∈ (wilsonIRSource C N p d x i k).support,
      w m * |MvPolynomial.coeff m (wilsonIRSource C N p d x i k)|) =
    ∑ m ∈ (PowerSeries.coeff k film).support,
      w (m.mapDomain (RG09.Walls.assign G)) *
        ‖MvPolynomial.coeff m (PowerSeries.coeff k film)‖ := by
  exact realPolynomial_rename_weighted_mass (RG09.Walls.assign G)
    (physicalFilm_basis_coeff_conjugate C N p d x i hC k) w

end YM.Integration
