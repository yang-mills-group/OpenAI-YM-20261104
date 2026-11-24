import YM.Integration.WilsonMeasuredPublicEntranceReserveWallet
/-! The actual superpolynomial trial widths still fit inside the same
separated-support exponential room shared by all the finite original peers. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePeerWindow
open Function Filter Finset Asymptotics Lattice RG Wilson Marker QuadraticLocal
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerMixedCollarSubpower
open scoped Classical BigOperators Topology

theorem fraction (C:ℝ)(cp:0≤C):
    ∀ᶠ H:ℝ in atTop,C*(1+Real.log H)*(scale H)^3≤(Real.log H)^2/128:=by
  let coeff:=2048*(C+1)
  have pos:0<coeff:=by dsimp [coeff];positivity
  have tiny:=(isLittleO_log_rpow_rpow_atTop (3:ℝ) (show (0:ℝ)<1 by norm_num)).def (inv_pos.mpr pos)
  filter_upwards [Real.tendsto_log_atTop.eventually tiny,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with H g h
  let t:=Real.log H
  have t0:0<t:=(Real.exp_pos 1).trans_le h
  have t1:1≤t:=(Real.one_le_exp_iff.mpr zero_le_one).trans h
  have l:1≤Real.log t:=by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h
  have raw:(Real.log t)^3≤coeff⁻¹*t:=by
    change ‖(Real.log t)^(3:ℝ)‖≤coeff⁻¹*‖t^(1:ℝ)‖ at g
    simpa only [show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast,Real.rpow_one,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans l) _),Real.norm_of_nonneg t0.le] using g
  have run: coeff*(Real.log t)^3≤t:=by
    have bound:=mul_le_mul_of_nonneg_left raw pos.le
    rwa [←mul_assoc,mul_inv_cancel₀ pos.ne',one_mul] at bound
  change C*(1+t)*(1+max 0 (Real.log t))^3≤t^2/128
  rw [max_eq_right (zero_le_one.trans l)]
  calc
    _≤C*(2*t)*(2*Real.log t)^3:=by gcongr <;> linarith
    _≤_:=by
      dsimp [coeff] at run
      nlinarith only [mul_le_mul_of_nonneg_right run t0.le,mul_nonneg (pow_nonneg (zero_le_one.trans l) 3) t0.le]

variable {V:Type}[DecidableEq V]{J:Census V}
theorem applied (C:ℝ)(cp:0≤C)(n:ℕ)(load:∀s:J.Mode,s.val.card≤n):
    ∀ᶠ H:ℝ in atTop,∀w:V→ℝ,(∀v,0<w v) →
      (∀v,(w v)⁻¹≤Real.exp (C*(1+Real.log H)*(scale H)^3)) →
      ∀s:J.Mode,(Poly.toll (fun v=>w v^2) s)⁻¹≤Real.exp ((Real.log H)^2/128):=by
  filter_upwards [fraction (2*(n:ℝ)*C) (by positivity),eventually_ge_atTop (1:ℝ)] with H fit hH w wp wage s
  let u:=C*(1+Real.log H)*(scale H)^3
  have zp:1 ≤ scale H:=by dsimp [scale];linarith only [le_max_left 0 (Real.log (Real.log H))]
  have up:0≤u:=mul_nonneg (mul_nonneg cp (by linarith only [Real.log_nonneg hH])) (pow_nonneg (zero_le_one.trans zp) _)
  have each(v:V):(w v^2)⁻¹≤Real.exp (2*u):=by
    rw [←inv_pow,show 2*u=u+u by ring,Real.exp_add,←sq]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (wp v).le) (wage v) _
  calc
    _=∏v∈s.val,(w v^2)⁻¹:=by simp [Poly.toll]
    _≤∏_v∈s.val,Real.exp (2*u):=Finset.prod_le_prod (fun v _=>(inv_nonneg.mpr (sq_nonneg (w v)))) (fun v _=>each v)
    _=Real.exp (s.val.card*(2*u)):=by rw [Finset.prod_const,Real.exp_nat_mul]
    _≤_:=Real.exp_le_exp.mpr (calc
      _≤(n:ℝ)*(2*u):=by gcongr;exact load s
      _≤_:=by dsimp only [u];linear_combination fit)

end YM.Integration.WilsonMeasuredPublicEntrancePeerWindow
end
