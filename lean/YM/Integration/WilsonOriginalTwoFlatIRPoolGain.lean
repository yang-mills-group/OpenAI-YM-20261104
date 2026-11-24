import YM.Integration.WilsonOriginalTwoFlatIRSocketHeardCell

noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolGain
open Finset WilsonPositionThermometerConnected
local notation "Faces" => Finset (Fin 3)

/-- Reserve twice the cofactor debit before the seven signed faces are withdrawn. -/
theorem seven (p q:Faces→ℂ){g B A:ℝ}(gp:0<g)(g1:g ≤ 1)(bp:1 ≤ B)(an:0 ≤ A)(P e:ℕ)
    (cap:∀s,‖p s‖ ≤ B*(g⁻¹)^e)
    (each:∀s:Faces,s.Nonempty → ‖p s-q s‖ ≤ A*g^(P+2*e)):
    ‖value p-value q‖ ≤ (21*(B+A)^2*A)*g^P:=by
  let k:=(g⁻¹)^e
  have k1:1 ≤ k:=one_le_pow₀ ((one_le_inv₀ gp).mpr g1)
  have kn:0 ≤ k:=zero_le_one.trans k1
  have H:1 ≤ B+A:=by linarith
  have eps:A*g^(P+2*e) ≤ A:=(mul_le_mul_of_nonneg_left (pow_le_one₀ gp.le g1) an).trans_eq (mul_one _)
  let M:=max 1 (max (B*k) (B*k+A))
  have mp:1 ≤ M:=le_max_left ..
  have roof:M ≤ (B+A)*k:=by
    have bound:B*k+A ≤ (B+A)*k:=by rw [add_mul]; linarith only [mul_le_mul_of_nonneg_left k1 an]
    exact max_le ((one_le_mul_of_one_le_of_one_le H k1)) (max_le ((le_add_of_nonneg_right an).trans bound) bound)
  have sq:M^2 ≤ ((B+A)*k)^2:=pow_le_pow_left₀ (zero_le_one.trans mp) roof _
  have am:M ≤ M^2:=by nlinarith [mul_nonneg (sub_nonneg.mpr mp) (zero_le_one.trans mp)]
  have sec:=WilsonOriginalTwoFlatIRSocketHeardCell.seven p q (B*k) A (A*g^(P+2*e))
    (mul_nonneg an (pow_nonneg gp.le _)) eps cap each
  calc
    _ ≤ 7*(M+2*M^2)*(A*g^(P+2*e)):=sec
    _ ≤ 7*(3*((B+A)*k)^2)*(A*g^(P+2*e)):=by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg an (pow_nonneg gp.le _))
      nlinarith only [sq,am]
    _ = (21*(B+A)^2*A)*g^P:=by
      dsimp [k]
      rw [pow_add,Nat.mul_comm 2 e,pow_mul,inv_pow]
      field_simp [gp.ne']
      ring

end YM.Integration.WilsonOriginalTwoFlatIRPoolGain
end
