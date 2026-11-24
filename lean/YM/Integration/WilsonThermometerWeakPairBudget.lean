import YM.Integration.WilsonThermometerWeakPairTriangle

/-! Separate physical root subtractions for a finite child and parent mode
bank. The total contains one copy of the relative gain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairBudget
open Finset
open scoped Classical BigOperators
variable {I J:Type}
theorem original (i:Finset I)(j:Finset J)(X:ℂ)(Y c:I→ℂ)(A v:J→ℂ)(B:I→J→ℂ)
    {W b q t:ℝ}(wp:0≤W)(bp:0≤b)(qp:0≤q)(tp:0≤t)
    (full:W*‖X-∑w∈j,A w*v w‖≤b*t)
    (outer:∀w∈j,W*‖A w-∑u∈i,c u*B u w‖≤b*q)
    (inner:∀u∈i,W*(‖c u‖*‖Y u-∑w∈j,B u w*v w‖)≤b*t):
    W*‖X-∑u∈i,c u*Y u‖ ≤ (1+(∑w∈j,‖v w‖)+i.card)*b*(t+q):=by
  have debt:=mul_le_mul_of_nonneg_left (WilsonThermometerWeakPairTriangle.account i j X Y c A v B) wp
  rw [mul_add,mul_add,mul_sum,mul_sum] at debt
  have D:∀w∈j,W*(‖A w-∑u∈i,c u*B u w‖*‖v w‖)≤(b*q)*‖v w‖:=fun w hw=>by
    rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (outer w hw) (norm_nonneg _)
  have h:=debt.trans (add_le_add (add_le_add full (sum_le_sum D)) (sum_le_sum inner))
  rw [←mul_sum,sum_const,nsmul_eq_mul] at h
  have nn:0≤∑w∈j,‖v w‖:=sum_nonneg (fun w _=>norm_nonneg _)
  have tq:t≤t+q:=le_add_of_nonneg_right qp
  have qt:q≤t+q:=le_add_of_nonneg_left tp
  calc
    _≤_:=h
    _≤b*(t+q)+(b*(t+q))*(∑w∈j,‖v w‖)+(i.card:ℝ)*(b*(t+q)):=by gcongr
    _=_:=by ring

end YM.Integration.WilsonThermometerWeakPairBudget
end
