import YM.Integration.WilsonSeparatedPrefixKineticDegree

/-! The two numerical terms in the socket estimate after the birth fee is restored. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedPrefixKineticCharge
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonReportingAbsoluteInletForecastBooks
open WilsonSeparatedPrefixKineticTruncation

theorem numerical (p h q:ℕ)(P:Cost){x y:ℝ}(x0:0<x)(x1:x ≤ 1)(y0:0<y)(xy:x/y ≤ 2)
    (cut:h+q+2 ≤ p)(print:(2:ℝ)^h*(h+2)*(mass p P)^h ≤ x⁻¹)
    (velocity:2*(h:ℝ)*3^h ≤ x⁻¹)(twice:(2:ℝ) ≤ x⁻¹)
    (numerical:|y-x*value p P x| ≤ x^(p+1)):
    (y^h)⁻¹*(x^(p+1)*((h:ℝ)+2)*(mass p P)^h+|(x*value p P x)^h-y^h|) ≤ x^q:=by
  let z:=(x/y)*value p P x
  have ratio:|z-1| ≤ 2*x^p:=by
    calc
      _=|y-x*value p P x|/y:=by rw [abs_sub_comm z 1,←abs_of_pos y0,←abs_div];congr 1;dsimp [z];field_simp;rw [abs_of_pos y0]
      _ ≤ x^(p+1)/y:=div_le_div_of_nonneg_right numerical y0.le
      _= (x/y)*x^p:=by rw [pow_succ];ring
      _ ≤ _:=mul_le_mul_of_nonneg_right xy (pow_nonneg x0.le _)
  have bounded:|z-1| ≤ 2:=by simpa only [mul_one] using ratio.trans (mul_le_mul_of_nonneg_left (pow_le_one₀ x0.le x1) (by norm_num))
  have limit:|z| ≤ 3:=by have s:=abs_le.mp bounded;apply abs_le.mpr;constructor <;> linarith only [s.1,s.2]
  have anchor:|z^h-1| ≤ 2*x^p*h*3^h:=by
    have price:=abs_pow_sub_pow_le z 1 h
    rw [one_pow] at price
    have money:max |z| |(1:ℝ)| ≤ 3:=max_le limit (by norm_num)
    exact price.trans (mul_le_mul (mul_le_mul_of_nonneg_right ratio (Nat.cast_nonneg h))
      ((pow_le_pow_left₀ ((abs_nonneg _).trans (le_max_left ..)) money _).trans (pow_le_pow_right₀ (by norm_num:1 ≤ (3:ℝ)) (by omega))) (by positivity) (by positivity))
  have pay (c:ℝ)(cost:c ≤ x⁻¹)(k:ℕ)(enough:q+2 ≤ k):c*x^k ≤ x^(q+1):=by
    calc
      _ ≤ x⁻¹*x^(q+2):=mul_le_mul cost (pow_le_pow_of_le_one x0.le x1 enough) (pow_nonneg x0.le _) (inv_nonneg.mpr x0.le)
      _ = _:=by rw [pow_succ];field_simp
  obtain ⟨k,rest⟩:=Nat.exists_eq_add_of_le (show h ≤ p+1 by omega)
  have ratioPower:(x/y)^h ≤ (2:ℝ)^h:=pow_le_pow_left₀ (div_nonneg x0.le y0.le) xy _
  have printed:(y^h)⁻¹*(x^(p+1)*((h:ℝ)+2)*(mass p P)^h) ≤ x^(q+1):=by
    calc
      _ = (x/y)^h*((h:ℝ)+2)*(mass p P)^h*x^k:=by rw [rest,pow_add,div_pow,div_eq_mul_inv];ring
      _ ≤ _:=pay _ ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ratioPower (by positivity)) (pow_nonneg (mass_nonneg ..) _)).trans print) _ (by omega)
  have normal:(y^h)⁻¹*|(x*value p P x)^h-y^h|=|z^h-1|:=by
    have equal:z*y=x*value p P x:=by dsimp [z];field_simp
    have restore:(x*value p P x)^h-y^h=(z^h-1)*y^h:=by rw [←equal,mul_pow,sub_mul,one_mul]
    rw [restore,abs_mul,abs_of_pos (pow_pos y0 h)]
    field_simp
  have fixed:(y^h)⁻¹*|(x*value p P x)^h-y^h| ≤ x^(q+1):=by
    rw [normal]
    calc
      _ ≤ _:=anchor
      _ = (2*(h:ℝ)*3^h)*x^p:=by ring
      _ ≤ _:=pay _ velocity _ (by omega)
  rw [mul_add]
  calc
    _ ≤ x^(q+1)+x^(q+1):=add_le_add printed fixed
    _ = (2*x)*x^q:=by rw [pow_succ];ring
    _ ≤ x^q:=by
      have one:2*x ≤ 1:=(mul_le_mul_of_nonneg_right twice x0.le).trans_eq (inv_mul_cancel₀ x0.ne')
      simpa only [one_mul] using mul_le_mul_of_nonneg_right one (pow_nonneg x0.le q)

end YM.Integration.WilsonSeparatedPrefixKineticCharge
end
