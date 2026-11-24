import YM.Integration.WilsonPhysicalHistoryFieldTail
import YM.Integration.FVA1Physical.Round2.FormalFieldOrder
import YM.MSbar.MeasureP.Pins
import YM.FormalBulk08.Lava.Ignis

/-! An ordered physical derivative of the filed torus polynomial reads its original
symmetric spatial kernel, including the factorial. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryFieldDerivatives
open Function Finset Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep RG16.Literal RG16.Guarding
open MSbar MSbar.Whisk Push.Uniform
open scoped Classical BigOperators
variable {G : Gauge} {d D : ℕ}

/-- The original site, oriented face and Lie coordinate, regrouped in formal-wire order. -/
def coordinates (G : Gauge) (n : Side) : Primary n G ≃ wire G n :=
  Equiv.prodAssoc (Site n) (TypeFace 1) G.ColorIndex

theorem site (n : Side) (a : Primary n G) :
    Measuring.chart n G a = (coordinates G n a).1 := rfl

private theorem word {V : Type} (r : ℕ) (P : MvPolynomial V ℝ) (v : Fin r → V) :
    Whisk.read 0 (List.ofFn v) P = climb r P v := by
  classical
  induction r generalizing P with
  | zero =>
    simp [Whisk.read, Cacao.spore, climb, MvPolynomial.constantCoeff_eq]
  | succ r ih =>
    rw [List.ofFn_succ]
    change Whisk.read 0 (List.ofFn (Fin.tail v)) (MvPolynomial.pderiv (v 0) P) =
      climb r (MvPolynomial.pderiv (v 0) P) (Fin.tail v)
    exact ih _ _

private theorem component {V : Type*} (r : ℕ) (P : MvPolynomial V ℝ) :
    climb r (MvPolynomial.homogeneousComponent r P) = climb r P := by
  classical
  induction r generalizing P with
  | zero => funext v; simp [climb, MvPolynomial.homogeneousComponent_zero]
  | succ r ih =>
    funext v
    change climb r (MvPolynomial.pderiv (v 0) (MvPolynomial.homogeneousComponent (r+1) P))
      (Fin.tail v) = climb r (MvPolynomial.pderiv (v 0) P) (Fin.tail v)
    rw [← Lava.comp_fuses, ih]

private theorem regroup {V W : Type*} (E : V ≃ W) (r : ℕ)
    (P : MvPolynomial W ℝ) (v : Fin r → V) :
    climb r (MvPolynomial.rename E.symm P) v = climb r P (E ∘ v) := by
  classical
  induction r generalizing P with
  | zero =>
    simpa [climb] using
      (MvPolynomial.coeff_rename_mapDomain E.symm E.symm.injective P 0)
  | succ r ih =>
    change climb r (MvPolynomial.pderiv (v 0) (MvPolynomial.rename E.symm P))
      (Fin.tail v) = climb r (MvPolynomial.pderiv (E (v 0)) P) (Fin.tail (E ∘ v))
    rw [show MvPolynomial.pderiv (v 0) (MvPolynomial.rename E.symm P) =
      MvPolynomial.rename E.symm (MvPolynomial.pderiv (E (v 0)) P) by
        simpa using MvPolynomial.pderiv_rename E.symm.injective (E (v 0)) P]
    exact ih _ _

/-- An actual ordered angular reading of the original, finite-period coefficient. -/
theorem kernel {V W : Type} [Fintype W] (E : V ≃ W) (r : ℕ)
    (P : MvPolynomial W ℝ) (v : Fin r → V) :
    Whisk.read 0 (List.ofFn v) (MvPolynomial.rename E.symm P) =
      (r.factorial : ℝ) * marble r P (E ∘ v) := by
  rw [word, regroup]
  have h : climb r P = (r.factorial : ℝ) • marble r P := by
    rw [← Lava.climb_read (marble_agate r P), marble_grade, component]
  exact congrFun h (E ∘ v)

/-- This is the same original formally filed insertion as the one on the measured R. -/
theorem filed (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
    (a : hue G) (depth : d<D) (N i e r : ℕ)
    (w : Letter (R.family.labels.level d)) (f : Studio D) (n : Side)
    (v : Fin r → Primary n G) :
    let Y := graph R L a depth N i
    Whisk.read 0 (List.ofFn v) (MvPolynomial.rename (coordinates G n).symm
      (PowerSeries.coeff e (Kemp.banner d (Y w f) n))) =
      (r.factorial : ℝ) * rancho (Kemp.banner d (Y w f) n) e r (coordinates G n ∘ v) :=
  kernel (coordinates G n) r _ v

end YM.Integration.WilsonPhysicalHistoryFieldDerivatives

