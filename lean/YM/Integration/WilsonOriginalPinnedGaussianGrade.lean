import YM.Integration.WilsonOriginalSingleMarkedRegister

/-! Read the full finite coupling coefficient on the named source, retaining distinct
signed and Laurent-weighted terms until after the original one-label log. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPinnedGaussianGrade
open Function Finset Marker Multi PowerSeries Comparison.RG02 Comparison.RG02.Order
open Integration.WilsonVacuumPreResetFiniteRegister
open PertExtension.Series Extra.Trajectories WilsonOriginalSingleMarkedRegister
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V](J:Census V)(r:ℕ)(s:J.Mode)
theorem original {A:Type}[Fintype A](a:A→ℂ)(P:A→PowerSeries ℝ)(j:ℕ)(hj:j≤r):
    (Order.observe J r (token J r s*(∑e,a e • register J r (P e))) j).part s=
      ∑e,a e*((coeff j (P e):ℝ):ℂ):=by
  rw [Order.observe,if_pos hj]
  change (j.factorial:ℂ)⁻¹*(token J r s*(∑e,a e • register J r (P e))).part (Join.pair s (Order.pick r j))=_
  rw [Finset.mul_sum,Poly.part_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [mul_smul_comm,Poly.part_smul,token_read J r _ _ _ _ (clean J r (P e)),
    if_pos rfl,WilsonVacuumPreResetFiniteRegister.read,Order.picked r hj,if_pos rfl]
  have nonzero:(j.factorial:ℂ)≠0:=by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [←mul_assoc,mul_comm _ (a e),mul_assoc,←mul_assoc (j.factorial:ℂ)⁻¹,(inv_mul_cancel₀ nonzero),one_mul]

end YM.Integration.WilsonOriginalPinnedGaussianGrade
