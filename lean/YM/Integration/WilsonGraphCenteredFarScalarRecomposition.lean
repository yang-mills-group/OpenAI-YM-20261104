import YM.Integration.WilsonGraphCenteredFarTwoClocks
import YM.Integration.WilsonGraphCenteredFarScalarOverflow

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedScalarRecomposition
open Finset PowerSeries Continuation
open MS.Book.Program
open scoped BigOperators Classical

theorem formal (A q : PowerSeries ℂ) (hq : Rooted q) :
    Appointed220.Eval.recompose A q = A.subst q := by
  ext n
  rw [Appointed220.Eval.recompose, coeff_mk, rules,
    YM.XSpace.FPS.coeff_substituted A ((coeff_zero_eq_constantCoeff_apply _).symm.trans hq)]
  have dom : Iic n = range (n+1) := by ext i; simp only [mem_Iic,mem_range]; omega
  rw [dom]
  apply sum_congr rfl
  intro i _
  simp only [cut,smul_eq_mul]
  exact mul_comm _ _

theorem value (p : ℕ) (t : ℝ) (A : PowerSeries ℂ) : crop p t A = Appointed220.Eval.value p A (t:ℂ) := by
  simp only [YM.FVA2.GradedFar.crop_eq, Appointed220.Eval.value, Appointed220.Eval.sumTo, smul_eq_mul]

theorem price (p : ℕ) (A q : PowerSeries ℂ) (hq : Rooted q) (v t : ℝ) (hv : |v|≤1) (ht : |t|≤1)
    (hw : ‖Appointed220.Eval.value p q (t:ℂ)‖≤1) (F : ℝ) (hF : 1≤F) (hM : Appointed220.Eval.mass p q≤F) :
    ‖crop p v A-crop p t (A.subst q)‖ ≤ Appointed220.Eval.mass p A*(p*
      ‖(v:ℂ)-Appointed220.Eval.value p q (t:ℂ)‖) +
      (p*F^p)*Appointed220.Eval.mass p A*|t|^(p+1) := by
  rw [value,value,← formal A q hq]
  have z : ‖(t:ℂ)‖≤1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using ht
  have v0 : ‖(v:ℂ)‖≤1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hv
  have first := Appointed220.Eval.lipschitz A p (v:ℂ) (Appointed220.Eval.value p q (t:ℂ)) v0 hw
  have last := Appointed220.Eval.payCompose A q p (t:ℂ) hq z hF hM
  simp only [Complex.norm_real,Real.norm_eq_abs] at last
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add first last)

end YM.FVA2.GradedFar.AppointedScalarRecomposition
