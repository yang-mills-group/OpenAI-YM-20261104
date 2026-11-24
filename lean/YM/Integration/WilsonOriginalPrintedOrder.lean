import YM.Integration.WilsonOriginalPrintedLength
import YM.Integration.WilsonEmittedOutputPower

/-! Price the native Laurent-restored regular crop at a prescribed coupling
order while allowing a signed winding discrepancy in every retained jet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrintedOrder
open WilsonEmittedOutputPower
open scoped BigOperators

theorem original {g W G a b cap τ ε C:ℝ}(pole debt P T:ℕ)
    (chosen:T=pole+debt+P)(positive:0<g)(small:g ≤ 1)(band:0 ≤ W)(held:W ≤ 2*g^(1/2:ℝ))
    (group:0 ≤ G)(cp:0 ≤ C)(length:b ≤ a*τ)
    (decay:τ ≤ g^T)(tp:0 ≤ τ)(inlet:G*a ≤ C*(g^debt)⁻¹)(long:cap ≤ C*(g^debt)⁻¹*τ):
    (g^pole)⁻¹*(G*((2*T:ℕ)*((3*T:ℕ)*ε+a*g^(3*T-2*T)+b)+a*W^(2*T))+g^pole*cap) ≤
      ((g^pole)⁻¹*(G*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)))*ε+(constant T+1)*C*g^P:=by
  have gT:0 ≤ g^T:=pow_nonneg positive.le _
  have c0:0 ≤ C*(g^debt)⁻¹:=by positivity
  have twice:1 ≤ (2:ℝ)^T:=one_le_pow₀ (by norm_num)
  have bright:=retained T positive band group c0
    (show 1*|G| *a ≤ C*(g^debt)⁻¹ by simpa [abs_of_nonneg group] using inlet)
    (show 1*|G| *b ≤ C*(g^debt)⁻¹*τ by
      rw [one_mul,abs_of_nonneg group]
      exact (mul_le_mul_of_nonneg_left length group).trans
        (by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right inlet tp))
    held (decay.trans (le_mul_of_one_le_left gT twice))
  rw [one_mul] at bright
  have pay:(g^pole)⁻¹*((g^debt)⁻¹*g^T)=g^P:=by
    rw [chosen,pow_add,pow_add]
    field_simp
  have restore:(g^debt)⁻¹*g^T ≤ g^P:=by
    rw [chosen,pow_add,pow_add,show (g^debt)⁻¹*(g^pole*g^debt*g^P)=g^pole*g^P by
      field_simp]
    exact mul_le_of_le_one_left (pow_nonneg positive.le _) (pow_le_one₀ positive.le small)
  have far:=long.trans ((mul_le_mul_of_nonneg_left decay c0).trans
    (show C*(g^debt)⁻¹*g^T ≤ C*g^P by rw [mul_assoc];exact mul_le_mul_of_nonneg_left restore cp))
  have fin:(g^pole)⁻¹*(constant T*(C*(g^debt)⁻¹)*g^T)=constant T*C*g^P:=by
    rw [←pay]
    ring
  calc
    _ = ((g^pole)⁻¹*(G*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)))*ε+
        (g^pole)⁻¹*(G*((2*T:ℕ)*(a*g^(3*T-2*T)+b)+a*W^(2*T)))+cap:=by
          field_simp
          ring
    _ ≤ ((g^pole)⁻¹*(G*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)))*ε+
        (g^pole)⁻¹*(constant T*(C*(g^debt)⁻¹)*g^T)+C*g^P:=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left bright (inv_nonneg.mpr (pow_nonneg positive.le pole)))) far
    _ = _:=by rw [fin];ring

end YM.Integration.WilsonOriginalPrintedOrder
end
