import YM.Integration.WilsonConditionalTaylorThermalInteractionDivision

/-! Mixed finite differences of normalized columns with all four original
vacuum factors. No restrictions are imposed on the common lower vertices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalMixedDivision
open PowerSeries WilsonConditionalTaylorThermalDivision
open scoped Classical BigOperators

def square {S : Type*} [Sub S] (origin a b joint : S) := (joint-a)-(b-origin)

theorem purchased {O A B T V D K G : PowerSeries ℝ} {w : ℕ}
    (pos : coeff 0 G ≠ 0) (old : zeroBefore O w)
    (left : zeroBefore (A-O) (w+2)) (right : zeroBefore (B-O) (w+2))
    (ka : zeroBefore (G-D) 2) (kb : zeroBefore (G-K) 2)
    (vac : zeroBefore (square V D K G) 4)
    (mixed : zeroBefore (square (O*V) (A*D) (B*K) (T*G)) (w+4)) :
    zeroBefore (square O A B T) (w+4) ∧
    coeff (w+4) (square O A B T)*coeff 0 G =
      coeff (w+4) (square (O*V) (A*D) (B*K) (T*G)) -
      coeff w O*coeff 4 (square V D K G) -
      coeff (w+2) (A-O)*coeff 2 (G-D) - coeff (w+2) (B-O)*coeff 2 (G-K) := by
  let X := square (O*V) (A*D) (B*K) (T*G) - O*square V D K G - (A-O)*(G-D) - (B-O)*(G-K)
  have price : X=square O A B T*G := by simp only [X,square];ring
  have asleep : zeroBefore X (w+4) := by
    intro i hi
    simp only [X,map_sub,mixed i hi,productLower old vac i hi,
      productLower left ka i hi,productLower right kb i hi,sub_zero]
  have invert := PowerSeries.mul_inv_cancel G (by simpa only [←coeff_zero_eq_constantCoeff_apply] using pos)
  have restore : square O A B T = X*G⁻¹ := by rw [price,mul_assoc,invert,mul_one]
  have free (S : PowerSeries ℝ) : zeroBefore S 0 := by intro i hi; omega
  have zero : zeroBefore (square O A B T) (w+4) := by
    rw [restore]
    simpa only [Nat.add_zero] using productLower asleep (free G⁻¹)
  refine ⟨zero,?_⟩
  have h := congrArg (coeff (w+4) (R:=ℝ)) price
  have leading := productFirst zero (free G)
  simp only [Nat.add_zero] at leading
  rw [leading] at h
  simpa only [X,map_sub,productFirst old vac,productFirst left ka,productFirst right kb] using h.symm

end YM.Integration.WilsonConditionalTaylorThermalMixedDivision
