import YM.Integration.WilsonOriginalObservedRoseScaledWallet

/-! Fix the high-order cutoff before the width of the retained optical corridor. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOriginalObservedRoseStoppedSalary

def stop (P D A:ℕ):ℕ:=P+D+12+A*14+3

private theorem powers {g:ℝ}(pos:0<g)(small:g≤1)(P d J:ℕ)(room:P+d≤J):
    (g⁻¹)^d*g^J≤g^P:=by
  obtain ⟨extra,eq⟩:=Nat.exists_eq_add_of_le room
  have unit:(g⁻¹)^d * g^d=1:=by rw [←mul_pow,inv_mul_cancel₀ pos.ne',one_pow]
  calc (g⁻¹)^d*g^J=(g^P*g^extra)*((g⁻¹)^d*g^d):=by rw [eq,pow_add,pow_add];ring
       _≤g^P:=by rw [unit,mul_one];exact mul_le_of_le_one_right (pow_nonneg pos.le _) (pow_le_one₀ pos.le small)

theorem original (P D A h:ℕ)(bound:h≤14){r g M B X τ C gap:ℝ}
    (rp:0≤r)(pos:0<g)(small:g≤1)(bpos:0≤B)(_xpos:0≤X)(tpos:0≤τ)(cpos:0≤C)
    (top:r^h*M≤B*(g⁻¹)^12*(g⁻¹)^(A*h+1))(test:τ≤X*(g⁻¹)^D)
    (gross:gap≤M*(τ*(C*g^(stop P D A))))(liquid:B*X*C≤g⁻¹):
    r^h*gap≤g^P:=by
  have zp:0≤g⁻¹:=(inv_pos.mpr pos).le
  let d:=12+(A*h+1)+D
  have subtotal:r^h*gap≤(B*X*C)*(g⁻¹)^d*g^(stop P D A):=by
    calc r^h*gap≤r^h*(M*(τ*(C*g^(stop P D A)))):=mul_le_mul_of_nonneg_left gross (pow_nonneg rp _)
         _=(r^h*M)*τ*C*g^(stop P D A):=by ring
         _≤(B*(g⁻¹)^12*(g⁻¹)^(A*h+1))*(X*(g⁻¹)^D)*C*g^(stop P D A):=by gcongr
         _=(B*X*C)*(g⁻¹)^d*g^(stop P D A):=by dsimp only [d];rw [pow_add,pow_add];ring
  have room:P+(d+1)≤ stop P D A:=by
    have x:=Nat.mul_le_mul_left A bound
    dsimp only [d,stop];omega
  calc r^h*gap≤(B*X*C)*(g⁻¹)^d*g^(stop P D A):=subtotal
       _≤g⁻¹*(g⁻¹)^d*g^(stop P D A):=by gcongr
       _=(g⁻¹)^(d+1)*g^(stop P D A):=by rw [pow_succ];ring
       _≤g^P:=powers pos small P (d+1) _ room

end YM.Integration.WilsonOriginalObservedRoseStoppedSalary
end
