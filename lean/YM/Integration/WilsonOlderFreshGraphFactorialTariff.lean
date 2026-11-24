import YM.Integration.WilsonOlderFreshGraphReceivingFigure

/-! The exponential is kept once when the order of the actual invoice is
decreased. This comparison allows a large, genuine spatial width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphFactorialTariff
open scoped BigOperators Classical

theorem lower {θ:ℝ}(pos:0<θ){n h:ℕ}(le:n≤h):
    θ⁻¹^n*(n.factorial:ℝ) ≤ θ⁻¹^h*(h.factorial:ℝ)*Real.exp θ:=by
  obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le le
  have perm:(n.factorial:ℝ)*(t.factorial:ℝ) ≤ ((n+t).factorial:ℝ):=by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n t)
  have radii:θ^t ≤ Real.exp θ*(t.factorial:ℝ):=
    (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp _ pos.le _)
  have cancel:θ⁻¹^t*θ^t=1:=by rw [←mul_pow,inv_mul_cancel₀ pos.ne',one_pow]
  calc
    _=θ⁻¹^(n+t)*θ^t*(n.factorial:ℝ):=by rw [pow_add,mul_assoc _ _ (θ^t),cancel,mul_one]
    _≤θ⁻¹^(n+t)*(Real.exp θ*(t.factorial:ℝ))*(n.factorial:ℝ):=by gcongr
    _=θ⁻¹^(n+t)*((n.factorial:ℝ)*(t.factorial:ℝ))*Real.exp θ:=by ring
    _≤_:=by gcongr

theorem exponential {θ:ℝ}(pos:0<θ)(n:ℕ):
    Real.exp (θ/2) ≤ (2:ℝ)^n*(θ⁻¹^n*(n.factorial:ℝ)*Real.exp θ):=by
  have half:0<θ/2:=by positivity
  have cash:(θ/2)^n ≤ Real.exp (θ/2)*(n.factorial:ℝ):=
    (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp _ half.le _)
  have unit:1 ≤ (Real.exp (θ/2)*(n.factorial:ℝ))/(θ/2)^n:=
    (le_div_iff₀ (by positivity)).mpr (by simpa using cash)
  have split:Real.exp θ=Real.exp (θ/2)*Real.exp (θ/2):=by rw [←Real.exp_add];congr 1;ring
  have inverse:((θ/2)^n)⁻¹ = (2:ℝ)^n*θ⁻¹^n:=by rw [←inv_pow,inv_div,div_eq_mul_inv,mul_pow]
  calc
    _=1*Real.exp (θ/2):=by simp
    _≤((Real.exp (θ/2)*(n.factorial:ℝ))/(θ/2)^n)*Real.exp (θ/2):=by gcongr
    _=_:=by rw [div_eq_mul_inv,inverse,split];ring

end YM.Integration.WilsonOlderFreshGraphFactorialTariff
end
