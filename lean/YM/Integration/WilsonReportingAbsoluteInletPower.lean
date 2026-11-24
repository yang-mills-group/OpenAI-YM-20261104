import Mathlib

/-! The unspecified offset tolerance pays the actual basis constant.
All three exponents are fixed before the cutoff and period. -/
set_option autoImplicit false
namespace YM.Integration.WilsonReportingAbsoluteInletPower
theorem paid {g A C ε:ℝ} (gp:0<g) (unit:g≤1) (ep:0<ε) {q w H p:ℕ} (order:q+w+H≤p)
    (invoice: |A| ≤ (ε/(1+|C|))*g^p*(C/g^H)) :
    |A|/g^w≤ε*g^q:=by
  have positive:0<(1:ℝ)+|C|:=by positivity
  have ct:C/(1+|C|)≤1:=(div_le_one positive).2 ((le_abs_self _).trans (by linarith only [abs_nonneg C]))
  have cp:0≤C:=by
    by_contra! negative
    have cost:C/g^H<0:=div_neg_of_neg_of_pos negative (pow_pos gp _)
    have bad:ε/(1+|C|)*g^p*(C/g^H)<0:=mul_neg_of_pos_of_neg (mul_pos (div_pos ep positive) (pow_pos gp _)) cost
    exact (not_lt_of_ge (abs_nonneg A)) (invoice.trans_lt bad)
  have powers:g^p≤g^(q+w+H):=pow_le_pow_of_le_one gp.le unit order
  calc
    |A|/g^w≤((ε/(1+|C|))*g^p*(C/g^H))/g^w:=div_le_div_of_nonneg_right invoice (pow_nonneg gp.le _)
    _≤((ε/(1+|C|))*g^(q+w+H)*(C/g^H))/g^w:=by
      gcongr
    _=(ε*(C/(1+|C|)))*g^q:=by rw [pow_add,pow_add];field_simp [gp.ne',positive.ne']
    _≤(ε*1)*g^q:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ct ep.le) (pow_nonneg gp.le _)
    _=ε*g^q:=by rw [mul_one]
end YM.Integration.WilsonReportingAbsoluteInletPower
