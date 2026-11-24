import YM.Integration.WilsonOriginalNullBareScale
import YM.Integration.WilsonOriginalNullBareTariff

/-! Combining the original regular and hard capital with the measured positive-rank panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareGross

def price (A C I W:ℝ) (k:ℕ):ℝ:=
  let b:=C*(A+1)
  b+32*|I| *(A*2^k+8*|W| *b+b)

theorem original {H g μ w E B J A C I W:ℝ} (k:ℕ)
    (warm:1≤H) (gp:0<g) (g1:g≤1) (gm:g⁻¹≤2*(1+H)) (mp:0≤μ) (mk:μ≤8*H)
    (wp:0<w) (ep:0≤E) (bp:0≤B) (cp:0≤C) (ap:0≤A)
    (income:E≤A*H) (rent:w*B≤C*H^2*E+C)
    (read:J ≤ 2*(I*g^3)*((E/w)/g^k+μ*(W*B)+B)):
    w*(B+2*μ*J) ≤ price A C I W k*(1+H)^(k+5) :=by
  let h:=1+H
  let b:=C*(A+1)
  have h1:1≤h:=by dsimp [h];linarith only [warm]
  have h0:0≤h:=zero_le_one.trans h1
  have hh:H≤h:=by dsimp [h];linarith
  have hp:0≤H:=zero_le_one.trans warm
  have b0:0≤b:=by dsimp [b];positivity
  have gpow:0≤g^k:=(pow_nonneg gp.le _)
  have wagt:0≤w*B:=mul_nonneg wp.le bp
  have spent:w*B≤b*h^3:=by
    calc
      w*B ≤ C*H^2*E+C:=rent
      _ ≤ C*h^2*(A*h)+C*h^3:=add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hh 2) cp)
          (income.trans (mul_le_mul_of_nonneg_left hh ap)) ep (by positivity))
        (le_mul_of_one_le_right cp (one_le_pow₀ h1))
      _ = b*h^3:=by dsimp [b];ring
  have pg:(g⁻¹)^k ≤ (2*h)^k:=pow_le_pow_left₀ (inv_nonneg.mpr gp.le) gm k
  have base:E/g^k ≤ A*2^k*h^(k+4):=by
    calc
      E/g^k=E*(g⁻¹)^k:=by rw [div_eq_mul_inv,inv_pow]
      _ ≤ (A*h)*(2*h)^k:=mul_le_mul (income.trans (mul_le_mul_of_nonneg_left hh ap)) pg
        (by positivity) (by positivity)
      _ = A*2^k*h^(k+1):=by rw [mul_pow,pow_succ];ring
      _ ≤ A*2^k*h^(k+4):=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) (by positivity)
  have regular:w*B≤b*h^(k+4):=spent.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ h1 (by omega)) b0)
  have wrap:μ*(|W| *(w*B)) ≤ 8*|W| *b*h^(k+4):=by
    calc
      _ ≤ (8*h)*(|W| *(b*h^3)):=mul_le_mul (mk.trans (by linarith only [hh]))
        (mul_le_mul_of_nonneg_left spent (abs_nonneg _)) (mul_nonneg (abs_nonneg _) wagt) (by positivity)
      _ = (8*|W| *b)*h^4:=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) (by positivity)
  let D:=A*2^k+8*|W| *b+b
  have D0:0≤D:=by dsimp [D];positivity
  have prod:|E/g^k+μ*(W*(w*B))+w*B| ≤ D*h^(k+4):=by
    calc
      _ ≤ |E/g^k|+|μ*(W*(w*B))|+|w*B|:=(abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
      _ = E/g^k+μ*(|W| *(w*B))+w*B:=by
        simp only [abs_mul,abs_of_nonneg bp,abs_of_nonneg wp.le,abs_of_nonneg mp,
          abs_of_nonneg (div_nonneg ep gpow)]
      _ ≤ A*2^k*h^(k+4)+8*|W| *b*h^(k+4)+b*h^(k+4):=add_le_add (add_le_add base wrap) regular
      _ = D*h^(k+4):=by dsimp [D];ring
  have scaled:w*J≤2*|I| *D*h^(k+4):=by
    calc
      w*J ≤ w*(2*(I*g^3)*((E/w)/g^k+μ*(W*B)+B)):=mul_le_mul_of_nonneg_left read wp.le
      _ = 2*(I*g^3)*(E/g^k+μ*(W*(w*B))+w*B):=by field_simp [wp.ne',gp.ne']
      _ ≤ |2*(I*g^3)*(E/g^k+μ*(W*(w*B))+w*B)|:=le_abs_self _
      _ = (2*|I| *g^3)*|E/g^k+μ*(W*(w*B))+w*B|:=by
        simp only [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num),abs_of_nonneg (pow_nonneg gp.le 3)]
        ring
      _ ≤ (2*|I|)*(D*h^(k+4)):=mul_le_mul
        (mul_le_of_le_one_right (by positivity) (pow_le_one₀ gp.le g1)) prod (abs_nonneg _) (by positivity)
      _ = _:=by ring
  calc
    _ = w*B+2*μ*(w*J):=by ring
    _ ≤ b*h^(k+5)+(2*(8*h))*(2*|I| *D*h^(k+4)):=add_le_add
      (spent.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) b0))
      ((mul_le_mul_of_nonneg_left scaled (by positivity)).trans
        (mul_le_mul_of_nonneg_right (by linarith only [mk,hh]) (by positivity)))
    _ = _:=by simp only [price,D,b,h,pow_add];ring
end YM.Integration.WilsonOriginalNullBareGross
