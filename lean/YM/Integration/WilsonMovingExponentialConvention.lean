import YM.FormalBulk08.Series.Canopy
import YM.MSbar.Cacao.Flow

/-! The two finite conventions for the exponential of the positive action.
Every factorial belongs to the same coupling index before a field is read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingExponentialConvention
open PowerSeries FormalBulk08.Series MSbar.Cacao
open scoped Classical BigOperators
variable {A B : Type} [CommRing A] [Algebra ℝ A] [Algebra ℚ A] [IsScalarTower ℚ ℝ A]

theorem exp (f : PowerSeries A) (h : Kind f) :
    FormalBulk08.Series.expan f = MSbar.Cacao.Spring f := by
  apply PowerSeries.ext
  intro n
  rw [expan, subst_coeff h _ n n le_rfl, MSbar.Cacao.Spring,coeff_mk, MSbar.Cacao.Aroma,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [PowerSeries.coeff_exp, PowerSeries.coeff_smul,Algebra.smul_def]
  congr 1
  rw [IsScalarTower.algebraMap_apply ℚ ℝ A]
  simp

variable [CommRing B] [Algebra ℝ B] [Algebra ℚ B] [IsScalarTower ℚ ℝ B]
theorem mapped (e : A→ₐ[ℝ]B) (f : PowerSeries A) (h : Kind f) :
    PowerSeries.map e.toRingHom (FormalBulk08.Series.expan f) =
      FormalBulk08.Series.expan (PowerSeries.map e.toRingHom f) := by
  have hh : Kind (PowerSeries.map e.toRingHom f) := by
    rw [Kind, PowerSeries.coeff_map, show coeff 0 f = 0 from h,map_zero]
  rw [exp f h, exp _ hh, MSbar.Cacao.sunshine]

end YM.Integration.WilsonMovingExponentialConvention
end
