import YM.Integration.WilsonCloseCaptureDate
import YM.Integration.WilsonConditionalTaylorCloseCost
import YM.Integration.WilsonConditionalTaylorWheelSeparatedBirth

/-! The true affine inverse temperature and the real close-capture scale
window pay for its variable number of dated connected transitions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonConditionalTaylorWheelShortClock
open Filter RG RG16 Wilson Lattice Real OPE WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open Next.Rank PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "V" => R.family.path.levels
local notation "H" => R.family.path.levels.clock.hatBeta

theorem affine (b m:ℕ):H m-H b=G.slopeConstant*(R.family.S.scale m-R.family.S.scale b):=by
  unfold Calendar.hatBeta
  change _+_*(R.family.S.scale m)-(_+_*(R.family.S.scale b))=_
  ring

include simple in
theorem half (K:ℝ) (pos:0 ≤ K):
    ∀ᶠ m:ℕ in atTop,∀ b:ℕ,R.family.S.scale m-R.family.S.scale b ≤ K*Real.log (Lambda V m) → H m ≤ 2*H b:=by
  let C:=G.slopeConstant*K
  have c0:0 ≤ C:=mul_nonneg (Gauge.slopeConstant_pos simple).le pos
  have rate:Tendsto H atTop atTop:=Next.Rank.Station.hat_rate V simple
  have price:0 < 4*(1+C):=by linarith
  have charge:=rate.eventually (Real.isLittleO_log_id_atTop.bound (inv_pos.mpr price))
  filter_upwards [charge,rate.eventually_ge_atTop (8*C)] with m spend warm b narrow
  have hp:0 < H m:=zero_lt_one.trans ((V).fits.delayed m)
  have hl:0 ≤ Real.log (H m):=Real.log_nonneg ((V).fits.delayed m).le
  have tiny:Real.log (H m) ≤ (4*(1+C))⁻¹*(H m):=by
    simpa only [Real.norm_eq_abs,id_eq,abs_of_pos hp,abs_of_nonneg hl] using spend
  have smaller:Real.log (H m)*(4*(1+C)) ≤ H m:=(le_div_iff₀ price).mp (by simpa only [div_eq_mul_inv,mul_comm] using tiny)
  have widened:Real.log (Lambda V m) ≤ 2+Real.log (H m):=Real.log_le_self (by unfold Lambda;linarith [hl])
  have paid:=mul_le_mul_of_nonneg_left widened c0
  have loss:=mul_le_mul_of_nonneg_left narrow (Gauge.slopeConstant_pos simple).le
  rw [←mul_assoc] at loss
  change H m ≤ 2*H b
  nlinarith only [affine R b m,loss,paid,smaller,warm,hl]

def toll (B:ℕ):Credit:=⟨1,1+2*((B+2:ℕ):ℝ)*(1+Real.log 4),by
  have a:0 ≤ Real.log 4:=Real.log_nonneg (by norm_num)
  linarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (B+2)) (show 0 ≤ 1+Real.log 4 by linarith)]⟩

theorem bound (B b m:ℕ) (warm:1 ≤ Real.log (H b)) (hot:H m ≤ 2*H b)
    (days:((m-b:ℕ):ℝ) ≤ R.family.S.scale m-R.family.S.scale b)
    (narrow:R.family.S.scale m-R.family.S.scale b ≤ ((B+2:ℕ):ℝ)*Real.log (Lambda V m)):
    R.family.S.scale m-R.family.S.scale b+((m-b:ℕ):ℝ) ≤ (toll B).buy (zz V b):=by
  let K:=((B+2:ℕ):ℝ)
  have kp:0 ≤ K:=by positivity
  have lb:0<Real.log (H b):=zero_lt_one.trans_le warm
  have hp:0 < H m:=zero_lt_one.trans ((V).fits.delayed m)
  have l:=Real.log_le_log hp hot
  rw [Real.log_mul (by norm_num) (ne_of_gt (zero_lt_one.trans ((V).fits.delayed b)))] at l
  have lm:0<Lambda V m:=by unfold Lambda;linarith [Real.log_nonneg ((V).fits.delayed m).le]
  have l2:Real.log 2 ≤ (1:ℝ):=by linarith only [Real.log_le_sub_one_of_pos (x:=(2:ℝ)) (by norm_num)]
  have up:Lambda V m ≤ 4*Real.log (H b):=by unfold Lambda;linarith
  have cut:=Real.log_le_log lm up
  rw [Real.log_mul (by norm_num) (ne_of_gt lb)] at cut
  have l4:0 ≤ Real.log 4:=Real.log_nonneg (by norm_num)
  have lb2:0 ≤ Real.log (Real.log (H b)):=Real.log_nonneg warm
  have area:Real.log (Lambda V m) ≤ (1+Real.log 4)*(zz V b):=by
    unfold zz
    nlinarith only [cut,mul_nonneg l4 lb2]
  have dur:(R.family.S.scale m-R.family.S.scale b)+((m-b:ℕ):ℝ) ≤ 2*(K*Real.log (Lambda V m)):=by
    dsimp only [K] at *
    linarith only [days,narrow]
  have one:0 ≤ zz V b:=by unfold zz;linarith
  change _ ≤ (1+2*K*(1+Real.log 4))*(zz V b)^1
  rw [pow_one]
  nlinarith only [dur,mul_le_mul_of_nonneg_left area kp,one]

end YM.Integration.WilsonConditionalTaylorWheelShortClock
end
