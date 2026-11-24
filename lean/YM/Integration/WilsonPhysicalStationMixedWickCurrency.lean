import YM.Integration.WilsonPhysicalStationGradedLowerPanel

/-! Restore the two independent Wick rank units in an actual measured entry.
The free off-rank term vanishes before multiplication by the clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickCurrency
open scoped Classical
theorem ratio (T:ℝ)(hot:1≤T)(q p:ℕ):T^q/T^p≤T^(q-p):=by
  rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hot) p)]
  exact (pow_le_pow_right₀ hot (show q≤(q-p)+p by omega)).trans_eq (pow_add T (q-p) p)

theorem restored {T A B:ℝ}(hot:1≤T)(nonneg:0≤A)(q p:ℕ)(value base:ℂ)
    (foreign:p≠q → base=0)(sale:A*T^((q-p:ℕ):ℝ)*‖value-base‖≤B):
    A*‖value*((T:ℂ)^q/(T:ℂ)^p)-base‖≤B:=by
  have pos:0<T:=lt_of_lt_of_le zero_lt_one hot
  have unit:(T:ℂ)≠0:=by exact_mod_cast pos.ne'
  have fixed:base*((T:ℂ)^q/(T:ℂ)^p)=base:=by
    by_cases equal:p=q
    · simp [equal,unit]
    · rw [foreign equal,zero_mul]
  rw [←fixed,←sub_mul,norm_mul,norm_div,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos pos,mul_comm ‖value-base‖,←mul_assoc]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ratio T hot q p) nonneg) (norm_nonneg _)).trans
    (by simpa only [Real.rpow_natCast] using sale)

end YM.Integration.WilsonPhysicalStationMixedWickCurrency
end
