import YM.Integration.WilsonEmittedSparseRows
import YM.WilsonCoeffUV.Emit.Expense

/-! The common axial cube on each actual period. Its circumference and
soft radius are bought before the original ultraviolet cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedCubeRoom
open Function Lattice RG Wilson Filter Real
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators
variable {G:Gauge} (A:Levels G) (tube : LinkTube G)

def roof (i:ℕ) := (A.budget i).B+1
def width (i:ℕ) := (A.budget i).threshold+(1+tube.constant)*axialCost (A.budget i) (roof A i)
def weight := 1+(1+tube.constant)*16*7^5*(Fintype.card PlaqAxes:ℝ)
private def bill : Credit := ⟨2,12+weight tube,by
  have hi : 0≤weight tube:=by unfold weight;positivity [tube.scale]
  linarith⟩

theorem side (simple:G.Simple) :
    ∀ᶠ i:ℕ in atTop, ∀q:ℕ, 2*roof A i < (A.S.side i q).val := by
  let K:=1+|A.clock.bar|+|G.slopeConstant|
  have Hrise:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [A.S.divergent.eventually_ge_atTop (12*K^2+30),Hrise.eventually_ge_atTop 1] with i rise one
  intro q
  let s:=A.S.scale i
  let H:=A.clock.hatBeta i
  have ks: 1 ≤ s:=by dsimp [s];nlinarith only [rise,sq_nonneg K]
  have β:1 ≤ H:=one
  have kt:0 ≤ K:=by dsimp [K];positivity
  have maxH:H≤K*s:=by
    have a:=le_mul_of_one_le_right (abs_nonneg A.clock.bar) ks
    have b:=mul_le_mul_of_nonneg_right (le_abs_self G.slopeConstant) (zero_le_one.trans ks)
    change A.clock.bar+G.slopeConstant*s≤(1+|A.clock.bar|+|G.slopeConstant|)*s
    nlinarith [le_abs_self A.clock.bar]
  have hlog:0 ≤ Real.log H:=Real.log_nonneg β
  have cap:((A.budget i).B:ℝ)≤(K*s)^2+1:=by
    change (Nat.ceil ((Real.log H)^2):ℝ)≤_
    have t:=Nat.ceil_lt_add_one (sq_nonneg (Real.log H))
    have u:Real.log H≤K*s:=(Real.log_le_self (zero_lt_one.trans_le β).le).trans maxH
    exact t.le.trans (add_le_add_left (pow_le_pow_left₀ hlog u 2) _)
  have grow:s^3/6≤Real.exp s:=by
    simpa only [show ((3:ℕ).factorial:ℝ)=6 by norm_num [Nat.factorial]] using Real.pow_div_factorial_le_exp s (zero_le_one.trans ks) 3
  have upper:2*(roof A i:ℝ)<Real.exp s:=by
    simp only [roof,Nat.cast_add,Nat.cast_one]
    apply lt_of_lt_of_le _ grow
    have cubic:=mul_nonneg (show 0≤ s-(12*K^2+30) from sub_nonneg.mpr rise) (sq_nonneg s)
    nlinarith [show 1≤ s^2 from one_le_pow₀ ks]
  have actual:Real.exp s = ((A.S.denominator i).val:ℝ):=by
    simp only [s,Schedule.scale,Schedule.a,inv_inv]
    exact Real.exp_log (by exact_mod_cast (A.S.denominator i).property)
  have bigger:(A.S.denominator i).val ≤ (A.S.side i q).val:=by
    change _ ≤ (A.S.period q).val*(A.S.denominator i).val
    exact Nat.le_mul_of_pos_left _ (A.S.period q).property
  rw [actual] at upper
  exact_mod_cast upper.trans_le (show ((A.S.denominator i).val:ℝ)≤(A.S.side i q).val by exact_mod_cast bigger)

theorem priced {i:ℕ} (large:1 ≤ Real.log (A.clock.hatBeta i)) :
    width A tube i ≤ A.clock.hatCoupling i * Real.exp ((bill tube).buy (zz A i)) := by
  let y:=Real.log (A.clock.hatBeta i)
  let z:=zz A i
  have hy:1≤y:=large
  have zy:Real.exp (z-1)=y:=by
    change Real.exp (1+Real.log y-1)=y
    rw [add_sub_cancel_left,Real.exp_log (zero_lt_one.trans_le hy)]
  have zz:1 ≤ z:=by change 1≤1+Real.log y;linarith [Real.log_nonneg hy]
  have D:(roof A i:ℝ)≤y^2+2:=by
    change ((Nat.ceil (y^2)+1:ℕ):ℝ)≤_
    push_cast
    linarith [Nat.ceil_lt_add_one (sq_nonneg y)]
  have narrow:2*(roof A i:ℝ)+1≤7*y^2:=by nlinarith [one_le_pow₀ hy (n:=2)]
  have fifth := pow_le_pow_left₀ (by positivity) narrow 5
  have Kpos:0≤weight tube:=by unfold weight;positivity [tube.scale]
  have ten := one_le_pow₀ hy (n:=10)
  have cal:(1+(1+tube.constant)*16*(2*(roof A i:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ))≤
      weight tube*y^10 :=by
    have debit:=mul_le_mul_of_nonneg_left fifth
      (show 0≤(1+tube.constant)*16*(Fintype.card PlaqAxes:ℝ) by positivity [tube.scale])
    unfold weight
    nlinarith only [debit,ten]
  have timed:(A.clock.monitor i)*(weight tube*y^10)≤ Real.exp ((bill tube).buy z) :=by
    rw [time_change A i,←zy,←Real.exp_nat_mul]
    change Real.exp ((z-1)^2)*(weight tube*Real.exp (10*(z-1)))≤_
    have expK:weight tube≤Real.exp (weight tube):=(Real.add_one_le_exp _).trans' (by linarith)
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right expK (Real.exp_pos _).le) (Real.exp_pos _).le)
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    change (z-1)^2+(weight tube+10*(z-1))≤(12+weight tube)*z^2
    have ZZ :=one_le_pow₀ zz (n:=2)
    have U:=mul_nonneg Kpos (sub_nonneg.mpr ZZ)
    nlinarith [mul_nonneg (zero_le_one.trans zz) (show 0≤z-1 by linarith)]
  change _≤A.clock.hatCoupling i*Real.exp ((bill tube).buy z)
  apply le_trans _ (mul_le_mul_of_nonneg_left timed (by unfold Calendar.hatCoupling;positivity))
  unfold width axialCost
  change A.clock.hatCoupling i*A.clock.monitor i+(1+tube.constant)*(16*(2*(roof A i:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(A.clock.hatCoupling i*A.clock.monitor i))≤_
  have h:=mul_le_mul_of_nonneg_left cal
    (show 0≤A.clock.hatCoupling i*A.clock.monitor i by unfold Calendar.hatCoupling Calendar.monitor;positivity)
  linarith only [h]

end YM.Integration.WilsonEmittedCubeRoom
end
