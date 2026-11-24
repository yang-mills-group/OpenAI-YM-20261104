import YM.Integration.WilsonIndependentWardFiniteBudget

/-! On the square-log inversion band a fixed-width physical aperture can be
absorbed by a spare period power. The measured source is multiplied once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardSquareLog

theorem aperture (k:ℕ)(D σ:ℝ)(hD:0<D)(hs:0<σ)(P a:ℝ)(hP:1≤P)(ha:0≤a)
    (band:(Real.log (1+a))^2≤D*Real.log P) :
    (1+a+Real.log P)^k ≤ Real.exp ((k:ℝ)^2/(4*(σ/D))) * (1+Real.log P)^k * P^σ := by
  have pp:0<P:=by linarith
  have pa:0<1+a:=by linarith
  have lp:=Real.log_nonneg hP
  let t:=σ/D
  have ht:0<t:=div_pos hs hD
  have htD:t*D=σ:=by dsimp [t];field_simp
  have q0:0≤t*((k:ℝ)/(2*t)-Real.log (1+a))^2:=mul_nonneg ht.le (sq_nonneg _)
  have sq:t*((k:ℝ)/(2*t)-Real.log (1+a))^2=(k:ℝ)^2/(4*t)+t*(Real.log (1+a))^2-(k:ℝ)*Real.log (1+a):=by
    field_simp [ne_of_gt ht]; ring
  rw [sq] at q0
  have limit:=mul_le_mul_of_nonneg_left band ht.le
  rw [←mul_assoc,htD] at limit
  have expbound:(1+a)^k≤Real.exp ((k:ℝ)^2/(4*t))*P^σ:=by
    rw [Real.rpow_def_of_pos pp,←Real.exp_add,←Real.exp_log pa,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    linarith [mul_comm (Real.log P) σ]
  have left:1+a+Real.log P≤(1+a)*(1+Real.log P):=by nlinarith [mul_nonneg ha lp]
  calc
    _ ≤ ((1+a)*(1+Real.log P))^k := pow_le_pow_left₀ (by linarith) left k
    _ = (1+a)^k*(1+Real.log P)^k := mul_pow .. 
    _ ≤ (Real.exp ((k:ℝ)^2/(4*t))*P^σ)*(1+Real.log P)^k :=
      mul_le_mul_of_nonneg_right expbound (pow_nonneg (by linarith) _)
    _ = _ := by unfold t; ring

theorem restored (k:ℕ)(D:ℝ)(hD:0<D)(M H P a v:ℝ)(hM:0≤M)(hH:0≤H)
    (hP:1≤P)(ha:0≤a)(band:(Real.log (1+a))^2≤D*Real.log P)
    (paid:v≤M*(H*(1+a+Real.log P)^k*P^(-(3/8:ℝ)))) :
    v ≤ M*((H*Real.exp ((k:ℝ)^2/(4*((1/8:ℝ)/D))))*(1+Real.log P)^k*P^(-(1/4:ℝ))) := by
  have pp:0<P:=by linarith
  have b:=aperture k D (1/8) hD (by norm_num) P a hP ha band
  apply paid.trans
  apply mul_le_mul_of_nonneg_left _ hM
  calc
    _ ≤ H*(Real.exp ((k:ℝ)^2/(4*((1/8:ℝ)/D)))*(1+Real.log P)^k*P^(1/8:ℝ))*P^(-(3/8:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b hH) (Real.rpow_nonneg pp.le _)
    _ = (H*Real.exp ((k:ℝ)^2/(4*((1/8:ℝ)/D))))*(1+Real.log P)^k*(P^(1/8:ℝ)*P^(-(3/8:ℝ))) := by ring
    _ = _ := by rw [←Real.rpow_add pp]; norm_num

end YM.Integration.WilsonIndependentWardSquareLog
