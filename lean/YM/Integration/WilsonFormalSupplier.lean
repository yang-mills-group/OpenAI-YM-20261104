import YM.Integration.WilsonPeriodization
import YM.RG06.Wilson.Kernel
import YM.RG06.Section.Floral

/-! Identify the exact RG06 formal stencil supplier before any product or
Wick contraction. This uses the same Family section, calibration, coefficient
order and engineering factor as the actual Wilson source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson PowerSeries RG06 RG06.WilsonCompiler
open scoped BigOperators Classical
variable {G : Gauge} (C : Family G) (d : ℕ)

theorem markTop_coeff_casing (v : C.label d) (k : ℕ) :
    PowerSeries.coeff k (markTop C d v) =
      Tokens.casing (C.localSection d) v k := by
  apply pigment_ext
  intro a
  have h := (gasket C d v (peeling G a)).coeff k
  rw [develop_coeff, access_peel] at h
  have h' := Tokens.wrapRule (C.localSection d) (peeling G a) v k
  change tone a (Tokens.casing (C.localSection d) v k) =
    GSeries.offer 0 k (fun t => (C.localSection d).evaluate v (roll (peeling G a) t)) at h'
  exact h.trans h'.symm

variable (N p : ℕ) (i : (C.labels.level d).Index)

theorem physicalCoverFilm_basis_coeff (k : ℕ) :
    PowerSeries.coeff (Tokens.charge i k)
      (physicalCoverFilm C N p d
        (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) =
      MvPolynomial.C (Dict06.Actual.factor C N d) *
        Tokens.stencil (C.localSection d) i k := by
  rw [physicalCoverFilm, Dict06.Actual.meet, (C.labels.level d).coords_basis,
    PowerSeries.coeff_C_mul, markTop_coeff_casing]
  rfl

/-- The real RG09 source is exactly the existing RG06 stencil, at its actual
shifted coefficient order, wrapped and put in the consumer's coordinates.
This proves source identification; it does not assert the IR quotient law. -/
theorem wilsonIRSource_formal_stencil (x : Site (C.side N p)) (k : ℕ) :
    wilsonIRSource C N p d x i (Tokens.charge i k) =
      MvPolynomial.rename (RG09.Walls.assign G)
        (realPolynomial (MvPolynomial.rename (coverAddress x)
          (MvPolynomial.C (Dict06.Actual.factor C N d) *
            Tokens.stencil (C.localSection d) i k))) := by
  rw [wilsonIRSource, physicalFilm_periodize, PowerSeries.coeff_map,
    physicalCoverFilm_basis_coeff]
  rfl

/-- The accepted Floral supplier on this very Family discharges the input
valuation condition. The lower coefficients vanish before any contraction. -/
theorem wilsonIRSource_below_grade {hG : G.Simple}
    (h : UVExtension.Oasis.Floral (hG := hG) C)
    (x : Site (C.side N p)) (k : ℕ) (hk : k < ((C.labels.level d).grades i).2) :
    wilsonIRSource C N p d x i k = 0 := by
  have hz : PowerSeries.coeff k
      (physicalCoverFilm C N p d
        (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) = 0 := by
    rw [physicalCoverFilm, Dict06.Actual.meet, (C.labels.level d).coords_basis,
      PowerSeries.coeff_C_mul, markTop_coeff_casing,
      Tokens.doesNotStart (C.localSection d) (Section.origin h d) i k hk, mul_zero]
  rw [wilsonIRSource, physicalFilm_periodize, PowerSeries.coeff_map, hz, map_zero]
  have hr : realPolynomial (0 : MvPolynomial (LinkVar G (Per (C.side N p))) ℂ) = 0 := by
    ext m
    simp [realPolynomial_coeff]
  rw [hr, map_zero]

end YM.Integration
