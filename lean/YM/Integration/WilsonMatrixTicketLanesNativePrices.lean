import YM.FVA2.LiftedLabels
import YM.FVAAlt2.Shop.Menus
import YM.Integration.WilsonCoefficientPreparation

/-! The compensated column of the prescribed physical observable in the two finite Wilson constructions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNativePrices
open FVA2 MS MS.Local.Physical PhysicalNext.Repeat.Legato PertExtension.LatticePT
open scoped Classical BigOperators
variable {G : Gauge}

def warehouse (R : Run G) : Warehouse G :=
  ⟨R.family.labels,R.family.params,R.family.localSection,R.makes.sections,CoefficientBridge.run_valuation R⟩

/-- These prices include every lower grade in the inverse finite Wick matrix. -/
theorem columns (V : Warehouse G) (B : Deck G) (d k : ℕ) (u : B.BIndex (d:ℤ) k)
    (i : (V.F.level d).Index) : (V.prices B d k u i : ℂ) =
      FVAAlt2.Shop.valueP B (V.S d) (V.h d) (V.acts d) u i := by
  let ξ := V.fits B d k u
  have separated : (∑ j, ξ j • (Pi.single j 1 : (V.scene d).Coeff)) = ξ := by
    ext j
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  have evaluated : V.qfits B d k u i = ∑ j, (ξ j) * topBasisComplex (V.S d) V.H (V.h d) (V.acts d) j i := by
    change ((V.scopeW d).inverse (Warehouse.inftyQ G) ξ) i = _
    conv_lhs => rw [← separated,map_sum]
    simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rfl
  have real_value : V.prices B d k u i = ∑ j, V.top B d k u j * topBasis (V.S d) V.H (V.h d) (V.acts d) j i := by
    change (V.qfits B d k u i).re = _
    rw [evaluated,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    change ((V.fits B d k u j) * _).re = _
    rw [← V.top_cast B u j,Complex.mul_re]
    simp [topBasis]
  rw [real_value]
  push_cast
  unfold FVAAlt2.Shop.valueP
  apply Finset.sum_congr rfl
  intro j _
  rw [V.top_cast B u j]
  rfl

/-- The exact actual registered source, slots, and retained covariance supply these prices on R. -/
theorem original (R : Run G) (B : Deck G) (d k : ℕ) (u : B.BIndex (d:ℤ) k)
    (i : (R.family.labels.level d).Index) : ((warehouse R).prices B d k u i : ℂ) =
      FVAAlt2.Shop.valueP B (R.family.localSection d) (R.makes.sections d)
        (CoefficientBridge.run_valuation R d) u i :=
  columns (warehouse R) B d k u i

end YM.Integration.WilsonMatrixTicketLanesNativePrices
