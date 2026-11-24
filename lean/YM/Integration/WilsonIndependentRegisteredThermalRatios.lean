import YM.Integration.WilsonVacuumPreResetSameTime
import YM.Next.RANK.Matrices

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentRegisteredThermalRatios
open Lattice RG Pressure Filter PhysicalNext.Repeat.Legato WilsonCoeffUV.Physical
open scoped Topology
variable {G:Gauge}

private theorem gentle {a b:ℝ}(ha:8≤a)(ab:a≤b)(hb:b≤2*a):
    (Real.log b)^2-(Real.log a)^2 ≤ b-a :=by
  have ap:0<a:=by linarith
  have bp:=ap.trans_le ab
  have log2:Real.log (2:ℝ) ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num:0<(2:ℝ))]
  have log8:Real.log (8:ℝ)≤3:=by
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num at *
    linarith
  have half:Real.log b ≤ a/2 :=by
    have t:=Real.log_le_sub_one_of_pos (div_pos bp (by norm_num:0<(8:ℝ)))
    rw [Real.log_div bp.ne' (by norm_num)] at t
    linarith
  have la:=Real.log_le_log ap ab
  have inc:=Real.log_le_sub_one_of_pos (div_pos bp ap)
  rw [Real.log_div bp.ne' ap.ne'] at inc
  have cost : (Real.log b-Real.log a)*a ≤ b-a :=by
    have c : Real.log b-Real.log a+1 ≤ b/a :=by linarith
    have c':=(le_div_iff₀ ap).mp c
    linarith
  calc
    _ = (Real.log b-Real.log a)*(Real.log b+Real.log a) :=by ring
    _ ≤ (Real.log b-Real.log a)*a := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr la)
    _ ≤ b-a:=cost

theorem temperatures {x y:ℝ}(hx:Real.exp 8≤x)(xy:x≤y)(yy:y≤2*x):
    temp x ≤ 2*temp y ∧ temp y ≤ 2*temp x :=by
  have xp : 0 < x := (Real.exp_pos _).trans_le hx
  have yp:=xp.trans_le xy
  have log2:Real.log (2:ℝ) ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num:0<(2:ℝ))]
  have a:8 ≤ Real.log x := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hx
  have ab:=Real.log_le_log xp xy
  have b:=Real.log_le_log yp yy
  rw [Real.log_mul (by norm_num) xp.ne'] at b
  have diff:=gentle a ab (by linarith)
  have up : Real.exp ((Real.log (Real.log y))^2) ≤ 2*Real.exp ((Real.log (Real.log x))^2) :=by
    apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity)).mp
    rw [Real.log_exp,Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp]
    linarith
  have ld:=Real.log_le_log (by linarith : 0<Real.log x) ab
  have la:0≤Real.log (Real.log x):=Real.log_nonneg (by linarith)
  have down : Real.exp ((Real.log (Real.log x))^2) ≤ Real.exp ((Real.log (Real.log y))^2) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ la ld 2)
  have sx:=Real.sqrt_pos.mpr xp
  have sy:=Real.sqrt_pos.mpr yp
  have sl:=Real.sqrt_le_sqrt xy
  have sr:Real.sqrt y≤2*Real.sqrt x := (Real.sqrt_le_left (by positivity)).2 (by nlinarith [Real.sq_sqrt xp.le])
  unfold temp
  simp only [inv_mul_eq_div,←mul_div_assoc]
  constructor
  · apply (div_le_div_iff₀ sx sy).mpr
    calc
      _ ≤ Real.exp ((Real.log (Real.log y))^2)*(2*Real.sqrt x) := mul_le_mul down sr sy.le (Real.exp_pos _).le
      _ = _ :=by ring
  · apply (div_le_div_iff₀ sy sx).mpr
    calc
      _ ≤ (2*Real.exp ((Real.log (Real.log x))^2))*Real.sqrt y := mul_le_mul up sl sx.le (by positivity)
      _ = _ :=by ring

theorem appointed (R:Run G)(hg:G.Simple):
    let A:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop, A.clock.threshold m≤2*A.clock.threshold (m+1) ∧
      A.clock.threshold (m+1)≤2*A.clock.threshold m:=by
  intro A
  filter_upwards [(RG01.Physical.hats hg A).eventually_ge_atTop (Real.exp 8),
    RG01.Physical.nextHat hg A] with m hot near
  exact temperatures hot (WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos hg).le (Nat.le_succ m)) near

end YM.Integration.WilsonIndependentRegisteredThermalRatios
