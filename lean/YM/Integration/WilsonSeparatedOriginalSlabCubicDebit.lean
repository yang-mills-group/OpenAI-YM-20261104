import YM.Integration.WilsonSeparatedOriginalMarkedCubic

/-! Exact sensitivity of the three-point cumulant to its seven measured moments. -/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalSlabCubicDebit
open Finset WilsonSeparatedOriginalMarkedCubic
open scoped Classical BigOperators
local notation "I"=>Fin 3
local notation "Row"=>Finset I

def pairFee (P Q:Row→ℂ)(e:Row→ℝ)(J K:Row):ℝ:=
  e J*‖P K‖+‖Q J‖*e K

def invoice (P Q:Row→ℂ)(e:Row→ℝ):ℝ:=
  e univ + (pairFee P Q e {0,1} {2}+pairFee P Q e {0,2} {1}+pairFee P Q e {1,2} {0})
  + 2*(pairFee P Q e {0} {1}*‖P {2}‖+‖Q {0}*Q {1}‖*e {2})

private theorem paired {x y a b:ℂ}{m n:ℝ}(mx:‖x-a‖ ≤ m)(ny:‖y-b‖ ≤ n):
    ‖x*y-a*b‖ ≤ m*‖y‖+‖a‖*n:=calc
  _ = ‖(x-a)*y+a*(y-b)‖:=by congr 1;ring
  _  ≤  ‖(x-a)*y‖+‖a*(y-b)‖:=norm_add_le .. 
  _  ≤  _:=by rw [norm_mul,norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_right mx (norm_nonneg _)) (mul_le_mul_of_nonneg_left ny (norm_nonneg _))

theorem original (P Q:Row→ℂ)(e:Row→ℝ)(paid:∀J,‖P J-Q J‖ ≤ e J):
    ‖cubic P-cubic Q‖ ≤ invoice P Q e:=by
  let x (J K:Row):=P J*P K-Q J*Q K
  let z:=P {0}*P {1}*P {2}-Q {0}*Q {1}*Q {2}
  have h (J K:Row):‖x J K‖ ≤ pairFee P Q e J K:=paired (paid J) (paid K)
  have ht:‖z‖ ≤ pairFee P Q e {0} {1}*‖P {2}‖+‖Q {0}*Q {1}‖*e {2}:=
    paired (h {0} {1}) (paid {2})
  have put:cubic P-cubic Q=(P univ-Q univ)-(x {0,1} {2}+x {0,2} {1}+x {1,2} {0})+2*z:=by
    dsimp [cubic,x,z];ring
  rw [put]
  apply (norm_add_le ..).trans
  apply add_le_add
  · apply (norm_sub_le ..).trans
    apply add_le_add (paid univ)
    apply (norm_add_le ..).trans
    exact add_le_add ((norm_add_le ..).trans (add_le_add (h _ _) (h _ _))) (h _ _)
  · rw [norm_mul,show ‖(2:ℂ)‖=2 by norm_num]
    exact mul_le_mul_of_nonneg_left ht (by norm_num)

end YM.Integration.WilsonSeparatedOriginalSlabCubicDebit
