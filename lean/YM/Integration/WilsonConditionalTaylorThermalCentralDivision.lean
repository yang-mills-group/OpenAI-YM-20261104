import YM.Integration.WilsonConditionalTaylorThermalMixedDivision

/-! Centering the two original normalizations removes all quadratic terms
from a single signed direction, through five relative coupling grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalCentralDivision
open PowerSeries WilsonConditionalTaylorThermalDivision

def direction (O V S Z : PowerSeries ℝ) := (O*Z-S)*V⁻¹

theorem original {A B O D K V S Z : PowerSeries ℝ} {w : ℕ} (pos : coeff 0 V ≠ 0)
    (old : zeroBefore O w) (first : zeroBefore (A-B) (w+2)) (temp : zeroBefore (D-K) 2)
    (evenN : zeroBefore ((A-O)+(B-O)) (w+4)) (evenV : zeroBefore ((D-V)+(K-V)) 4)
    (rawN : zeroBefore ((A*D-B*K)+(S+S)) (w+6)) (rawV : zeroBefore ((D-K)+(Z+Z)) 6) :
    zeroBefore ((A-B)-(direction O V S Z+direction O V S Z)) (w+6) := by
  let E := (A-B)*V+O*(D-K)-(A*D-B*K)
  have identity : E+E= -((A-B)*((D-V)+(K-V)))-((A-O)+(B-O))*(D-K) := by dsimp [E];ring
  have even : zeroBefore E (w+6) := by
    intro i hi
    have eq := congrArg (coeff i (R:=ℝ)) identity
    simp only [map_sub,map_add,map_neg,productLower first evenV i hi,
      productLower evenN temp i hi,neg_zero,sub_zero] at eq
    linarith
  let F := E+((A*D-B*K)+(S+S))-O*((D-K)+(Z+Z))
  have endprice : zeroBefore F (w+6) := by
    intro i hi
    simp only [F,map_sub,map_add,even i hi,rawN i hi,productLower old rawV i hi,add_zero,sub_zero]
  have unit := PowerSeries.mul_inv_cancel V (by simpa only [←coeff_zero_eq_constantCoeff_apply] using pos)
  have short : F=(A-B)*V-((O*Z-S)+(O*Z-S)) := by dsimp [F,E];ring
  have write : ((A-B)-(direction O V S Z+direction O V S Z))=F*V⁻¹ := by
    rw [short,sub_mul,add_mul,mul_assoc,unit,mul_one];rfl
  have free : zeroBefore V⁻¹ 0 := by intro i hi;omega
  rw [write]
  simpa only [Nat.add_zero] using productLower endprice free

end YM.Integration.WilsonConditionalTaylorThermalCentralDivision
