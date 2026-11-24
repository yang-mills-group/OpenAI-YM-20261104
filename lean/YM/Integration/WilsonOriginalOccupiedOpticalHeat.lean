import YM.Integration.WilsonOriginalOccupiedRate

/-! The exact flat original divisor pays every fixed power of the logarithmic mesh span. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedOpticalHeat
open Filter Push.Local WilsonThermometerMixedCollarSubpower
open private YM.Push.Local.mon YM.Push.Local.gasRate from YM.Push.LOCAL_SPLITTING.Delay
open scoped Topology

private theorem dominated (c:ℝ)(k:ℕ):
    ∀ᶠ x:ℝ in atTop,c*(Real.log x)^k ≤ (YM.Push.Local.mon x)^((1:ℝ)/5):=by
  have deep:=Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1:ℝ),deep.eventually_ge_atTop (max (5*((k:ℝ)+1)) |c|)] with x xp large
  let L:=Real.log x
  let y:=Real.log L
  have hl:0<L:=Real.log_pos xp
  have h1:5*((k:ℝ)+1) ≤ y:=(le_max_left ..).trans large
  have h2:|c| ≤ y:=(le_max_right ..).trans large
  have y0:0 ≤ y:=(abs_nonneg c).trans h2
  have ex:(Real.log x)^k=Real.exp ((k:ℝ)*y):=by rw [Real.exp_nat_mul,Real.exp_log hl]
  calc
    _ ≤ Real.exp |c| *Real.exp ((k:ℝ)*y):=by
      rw [ex];exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by linarith only [Real.add_one_le_exp |c|])) (Real.exp_pos _).le
    _ ≤ _:=by
      rw [←Real.exp_add,YM.Push.Local.mon,←Real.exp_mul]
      apply Real.exp_le_exp.2
      change |c| +k*y ≤ y^2*(1/5)
      nlinarith only [mul_nonneg (sub_nonneg.mpr h1) y0,h2]

theorem original (n d:ℕ)(C:ℝ)(c0:0 ≤ C):
    ∀ᶠ x:ℝ in atTop,∀l:ℕ, (l:ℝ) ≤ C*(1+Real.log x)^d →
      Real.exp (n*(l:ℝ)*(scale x)^3)*Real.sqrt (Real.sqrt (YM.Push.Local.gasRate x)) ≤ 1:=by
  let c:=4*(n:ℝ)*C*2^(d+3)
  filter_upwards [dominated c (d+3),Real.tendsto_log_atTop.eventually_ge_atTop 1] with x enough xp l span
  let L:=Real.log x
  have lp:0 ≤ L:=zero_le_one.trans xp
  have first:1+L ≤ 2*L:=by linarith
  have tail:scale x ≤ 2*L:=by
    have h:max 0 (Real.log L) ≤ L:=max_le lp (Real.log_le_self lp)
    change 1+max 0 (Real.log L) ≤ 2*L
    linarith only [xp,h,show Real.log x=L from rfl]
  have cash:4*(n:ℝ)*(l:ℝ)*(scale x)^3 ≤ (YM.Push.Local.mon x)^((1:ℝ)/5):=by
    have zp:0 ≤ scale x:=by unfold scale;linarith only [le_max_left 0 (Real.log (Real.log x))]
    have gross:(l:ℝ) ≤ C*(2*L)^d:=span.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) first _) c0)
    calc
      _ ≤ 4*(n:ℝ)*(C*(2*L)^d)*(2*L)^3:=mul_le_mul
        (mul_le_mul_of_nonneg_left gross (by positivity)) (pow_le_pow_left₀ zp tail _) (pow_nonneg zp _) (by positivity)
      _ = c*L^(d+3):=by dsimp [c];rw [pow_add,pow_add,mul_pow,mul_pow];ring
      _ ≤ _:=enough
  simp only [YM.Push.Local.gasRate,Real.sqrt_eq_rpow,←Real.exp_mul,←Real.exp_add]
  exact Real.exp_le_one_iff.2 (by linarith only [cash])

end YM.Integration.WilsonOriginalOccupiedOpticalHeat
