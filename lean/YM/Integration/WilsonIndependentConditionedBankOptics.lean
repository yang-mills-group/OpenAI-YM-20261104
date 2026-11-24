import YM.Integration.WilsonIndependentMovingFittedBracket

/-! Numerical order on an optical collar after the individual field and Gram salaries have been reported. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankOptics

theorem gross (h₀ h₁:ℕ)(δ ζ ν t F i B₀ B₁ G:ℝ)
    (pos:0<δ)(small:δ≤1)(gain:0≤ζ)(nu:0≤ν)(thermal:0≤t)(field:0≤F)(left:0≤B₀)(right:0≤B₁):
    let H:=h₀+h₁; let a:=B₀*(δ^h₀)⁻¹; let b:=B₁*(δ^h₁)⁻¹; let gram:=G*(δ^H)⁻¹
    (ν*(F*δ^ζ))*(i+2*t*(a+b))+3*t*(|gram| *a*b) ≤
    (ν*F*i)*δ^ζ+t*(δ^(2*H))⁻¹*(2*ν*F*(B₀+B₁)+3*|G| *B₀*B₁):=by
  intro H a b gram
  have one:=Real.rpow_le_one pos.le small gain
  have scale (h:ℕ)(B:ℝ)(size:h≤2*H)(paid:0≤B):
      δ^ζ*(B*(δ^h)⁻¹)≤B*(δ^(2*H))⁻¹:=by
    apply (mul_le_of_le_one_left (mul_nonneg paid (inv_nonneg.mpr (pow_nonneg pos.le _))) one).trans
    apply mul_le_mul_of_nonneg_left _ paid
    exact (inv_le_inv₀ (pow_pos pos _) (pow_pos pos _)).2 (pow_le_pow_of_le_one pos.le small size)
  have la:δ^ζ*a≤B₀*(δ^(2*H))⁻¹:=scale h₀ B₀ (by dsimp [H];omega) left
  have lb:δ^ζ*b≤B₁*(δ^(2*H))⁻¹:=scale h₁ B₁ (by dsimp [H];omega) right
  have exactGram:|gram| *a*b=|G| *B₀*B₁*(δ^(2*H))⁻¹:=by
    dsimp [gram,a,b,H]
    rw [abs_mul,abs_of_pos (inv_pos.mpr (pow_pos pos _))]
    simp only [two_mul,pow_add,mul_inv_rev]
    ring
  let f:=ν*F*i*δ^ζ+3*t*(|G| *B₀*B₁*(δ^(2*H))⁻¹)
  calc
    _=f+(2*ν*F*t)*(δ^ζ*a+δ^ζ*b):=by rw [exactGram];dsimp [f];ring
    _≤f+(2*ν*F*t)*(B₀*(δ^(2*H))⁻¹+B₁*(δ^(2*H))⁻¹):=
      add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add la lb) (mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) nu) field) thermal)) f
    _=_:=by dsimp [f];ring

theorem order (g δ a A ζ D P:ℝ)(q H:ℕ)(hot:0<g)(weak:g≤1)(gain:0≤ζ)
    (fine:δ≤g^a)(coarse:g^A≤δ)(secured:P+D≤a*ζ)(chosen:P+D≤((q+1:ℕ):ℝ)-A*H):
    g^(-D)*(δ^ζ+|g|^(q+1)*(δ^H)⁻¹) ≤ 2*g^P:=by
  have dp:0<δ:=(Real.rpow_pos_of_pos hot _).trans_le coarse
  have first:δ^ζ≤g^(P+D):=by
    apply (Real.rpow_le_rpow dp.le fine gain).trans
    rw [←Real.rpow_mul hot.le]
    exact Real.rpow_le_rpow_of_exponent_ge hot weak secured
  have second:|g|^(q+1)*(δ^H)⁻¹≤g^(P+D):=by
    have saved:=Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hot A) coarse
      (neg_nonpos.mpr (Nat.cast_nonneg H:0≤(H:ℝ)))
    rw [Real.rpow_neg dp.le,Real.rpow_natCast] at saved
    rw [abs_of_pos hot,←Real.rpow_natCast g (q+1)]
    apply (mul_le_mul_of_nonneg_left saved (Real.rpow_nonneg hot.le _)).trans
    rw [←Real.rpow_mul hot.le,←Real.rpow_add hot]
    apply Real.rpow_le_rpow_of_exponent_ge hot weak
    linarith
  calc
    _≤g^(-D)*(g^(P+D)+g^(P+D)):=mul_le_mul_of_nonneg_left (add_le_add first second) (Real.rpow_nonneg hot.le _)
    _=2*g^P:=by rw [←two_mul,mul_left_comm,←Real.rpow_add hot];congr 2;ring

end YM.Integration.WilsonIndependentConditionedBankOptics
