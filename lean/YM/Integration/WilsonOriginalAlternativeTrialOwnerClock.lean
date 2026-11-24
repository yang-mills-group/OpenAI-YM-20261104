import YM.Integration.WilsonOriginalAlternativeTrialScales

/-! Uniform clock for the actual upper guard and the authentic lower hard field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialOwnerClock
open Wilson RG WilsonThermometerMixedCollarSubpower

def allowance (power span:ℕ)(B:ℝ):ℝ:=
  (abs B)+2*(6+(power:ℝ))+1+8*(9*((span:ℝ)/Real.log 2)+6)+1

private theorem power_cost {H S:ℝ} (pos:0<H)(large:Real.log H  ≤  S)(d:ℕ):
    H^d  ≤  Real.exp ((d:ℝ)*S):=by
  rw [←Real.exp_log (pow_pos pos d),Real.log_pow]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left large (Nat.cast_nonneg d))

/-- The common log salary accounts for the complete genuine engineering amount
and the measured polylogarithmic width pressure over the whole optical interval. -/
theorem original {H T B M wage:ℝ} (power span length:ℕ) (hp:1  ≤  H) (tp:1  ≤  T)
    (comparable:T  ≤  H^2)(phase:scale T  ≤  2*scale H)
    (time:(length:ℝ)*Real.log 2  ≤  (span:ℝ)*Real.log H)
    (bp:0  ≤  B)(paid:M  ≤  B*T^power)
    (width:wage  ≤  H^(2*(6+power)+1)*Real.exp ((9*(length:ℝ)+6)*(scale T)^3)):
    let size:=(1+Real.log H)*(scale H)^3
    wage  ≤  Real.exp (allowance power span B*size) ∧
      T^6*M+wage  ≤  Real.exp (allowance power span B*size):=by
  intro size
  have hh:0<H:=zero_lt_one.trans_le hp
  have ll:0 ≤ Real.log H:=Real.log_nonneg hp
  have sh:1  ≤  scale H:=by unfold scale; linarith only [le_max_left (0:ℝ) (Real.log (Real.log H))]
  have st:1  ≤  scale T:=by unfold scale; linarith only [le_max_left (0:ℝ) (Real.log (Real.log T))]
  have sh3:1 ≤ (scale H)^3:=one_le_pow₀ sh
  have head:0 ≤ 1+Real.log H:=by linarith
  have rent:1+Real.log H ≤ size:=le_mul_of_one_le_right head sh3
  have unit:1 ≤ size:=by linarith
  have sp:0 ≤ size:=zero_le_one.trans unit
  have logpay:Real.log H ≤ size:=by linarith
  have two:0<Real.log 2:=Real.log_pos (by norm_num)
  have slope:0 ≤ (span:ℝ)/Real.log 2:=div_nonneg (Nat.cast_nonneg _) two.le
  have days:(length:ℝ)  ≤  ((span:ℝ)/Real.log 2)*(1+Real.log H):=by
    calc
      (length:ℝ)  ≤  (span:ℝ)*Real.log H/Real.log 2:=(le_div_iff₀ two).mpr time
      _ = (span:ℝ)/Real.log 2*Real.log H:=by ring
      _  ≤  (span:ℝ)/Real.log 2*(1+Real.log H):=mul_le_mul_of_nonneg_left (by linarith) slope
  have shifted:9*(length:ℝ)+6 ≤ (9*((span:ℝ)/Real.log 2)+6)*(1+Real.log H):=by nlinarith
  have cube:(scale T)^3 ≤ 8*(scale H)^3:=by
    calc
      (scale T)^3  ≤  (2*scale H)^3:=pow_le_pow_left₀ (zero_le_one.trans st) phase 3
      _=8*(scale H)^3:=by ring
  have passage:(9*(length:ℝ)+6)*(scale T)^3  ≤  (8*(9*((span:ℝ)/Real.log 2)+6))*size:=by
    calc
      _  ≤  ((9*((span:ℝ)/Real.log 2)+6)*(1+Real.log H))*(8*(scale H)^3):=
        mul_le_mul shifted cube (pow_nonneg (zero_le_one.trans st) _) (by positivity)
      _=_:=by dsimp [size];ring
  let bill:=(abs B)+2*(6+(power:ℝ))+1+8*(9*((span:ℝ)/Real.log 2)+6)
  have growW : wage  ≤  Real.exp (bill*size):=by
    apply width.trans
    calc
      _  ≤  Real.exp (((2*(6+power)+1:ℕ):ℝ)*size)*Real.exp ((8*(9*((span:ℝ)/Real.log 2)+6))*size):=
        mul_le_mul (power_cost hh logpay _) (Real.exp_le_exp.mpr passage) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _  ≤  _:=by rw [←Real.exp_add]; apply Real.exp_le_exp.mpr;push_cast;dsimp [bill];nlinarith only [mul_nonneg (abs_nonneg B) sp]
  have before:(T^(6+power)) ≤ (H^(2*(6+power))):=by
    rw [pow_mul]
    exact pow_le_pow_left₀ (zero_le_one.trans tp) comparable _
  have cash:B ≤ Real.exp ((abs B)*size):=by
    have one:=Real.add_one_le_exp (abs B)
    have paid':(abs B) ≤ (abs B)*size:=le_mul_of_one_le_right (abs_nonneg _) unit
    exact (show B ≤ Real.exp (abs B) by linarith only [le_abs_self B,one]).trans (Real.exp_le_exp.mpr paid')
  have guard:T^6*M ≤ Real.exp (bill*size):=by
    calc
      _ ≤ T^6*(B*T^power):=mul_le_mul_of_nonneg_left paid (pow_nonneg (zero_le_one.trans tp) _)
      _=B*T^(6+power):=by rw [pow_add];ring
      _ ≤ B*H^(2*(6+power)):=mul_le_mul_of_nonneg_left before bp
      _ ≤ Real.exp ((abs B)*size)*Real.exp (((2*(6+power):ℕ):ℝ)*size):=
        mul_le_mul cash (power_cost hh logpay _) (pow_nonneg hh.le _) (Real.exp_nonneg _)
      _  ≤  _:=by
        rw [←Real.exp_add];apply Real.exp_le_exp.mpr;push_cast;dsimp [bill]
        nlinarith only [sp,mul_nonneg slope sp]
  have maxcost:Real.exp (bill*size)+Real.exp (bill*size) ≤ Real.exp (allowance power span B*size):=by
    have raise:2  ≤  Real.exp size:=by linarith only [Real.add_one_le_exp size,unit]
    calc
      _=2*Real.exp (bill*size):=by ring
      _ ≤ Real.exp size*Real.exp (bill*size):=mul_le_mul_of_nonneg_right raise (Real.exp_nonneg _)
      _=_:=by rw [←Real.exp_add];congr 1;unfold allowance;dsimp [bill];ring
  exact ⟨growW.trans ((le_add_of_nonneg_left (Real.exp_nonneg _)).trans maxcost),(add_le_add guard growW).trans maxcost⟩

end YM.Integration.WilsonOriginalAlternativeTrialOwnerClock
end
