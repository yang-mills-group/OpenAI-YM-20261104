import YM.Integration.WilsonOriginalAlternativeTrialClock

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialScales
open Function Filter Lattice Wilson RG Extra.Histories PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerMixedCollarSubpower
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "mesh" => R.family.S.a

private theorem ratio (f K:ℕ):Real.log (mesh f/mesh K)=R.family.S.scale K-R.family.S.scale f:=by
  rw [Real.log_div (R.family.S.a_pos f).ne' (R.family.S.a_pos K).ne']
  simp only [Schedule.scale,Real.log_inv];ring

private theorem dyadic (f n:ℕ):2^n≤(R.family.S.steps f n).val:=by
  induction n with
  | zero => simp [Schedule.steps]
  | succ n ih =>
    rw [pow_succ,Schedule.steps,PNat.mul_coe]
    exact Nat.mul_le_mul ih ((by norm_num:2≤3).trans (R.family.S.block_large _))

private theorem steps {f K:ℕ}(fk:f≤K):((K-f:ℕ):ℝ)*Real.log 2≤R.family.S.scale K-R.family.S.scale f:=by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le fk
  have size:((R.family.S.steps f n).val:ℝ)=mesh f/mesh (f+n):=by
    rw [Schedule.a,Schedule.a,Schedule.den_add,PNat.mul_coe,Nat.cast_mul]
    have dp:0<((R.family.S.denominator f).val:ℝ):=by exact_mod_cast (R.family.S.denominator f).property
    field_simp [dp.ne']
  have price:(2:ℝ)^n≤((R.family.S.steps f n).val:ℝ):=by exact_mod_cast dyadic R f n
  have log:=Real.log_le_log (show 0<(2:ℝ)^n by positivity) (price.trans_eq size)
  rwa [Real.log_pow,ratio,Nat.add_sub_cancel_left] at *

theorem original (simple:G.Simple)(a:ℕ):∀ᶠ f:ℕ in atTop,∀K,f≤K→mesh f/mesh K≤(H f)^a→
    H K≤(H f)^2 ∧ scale (H K)≤2*scale (H f) ∧
      ((K-f:ℕ):ℝ)*Real.log 2≤a*Real.log (H f):=by
  have rise:Tendsto H atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [rise.eventually_ge_atTop (1+G.slopeConstant*a),rise.eventually_ge_atTop (Real.exp 1)]
    with f upper warm K fk span
  have hp:1<H f:=(Real.one_lt_exp_iff.mpr zero_lt_one).trans_le warm
  have hk:1<H K:=(R.family.path.levels.fits.delayed K)
  have logK:=Real.log_le_log (div_pos (R.family.S.a_pos f) (R.family.S.a_pos K)) span
  rw [ratio,Real.log_pow] at logK
  have values:H K=H f+G.slopeConstant*(R.family.S.scale K-R.family.S.scale f):=by unfold Calendar.hatBeta;ring
  have budget:H K≤(H f)^2:=by
    have tide:=mul_le_mul_of_nonneg_left logK (Gauge.slopeConstant_pos simple).le
    have small:=Real.log_le_self (zero_le_one.trans hp.le)
    have cap:=mul_le_mul_of_nonneg_right upper (zero_le_one.trans hp.le)
    nlinarith only [values,tide,mul_le_mul_of_nonneg_left small (mul_nonneg (Gauge.slopeConstant_pos simple).le (Nat.cast_nonneg a)),cap]
  refine ⟨budget,?_,(steps R fk).trans logK⟩
  have logs:=Real.log_le_log (zero_lt_one.trans hk) budget
  rw [Real.log_pow] at logs
  have small:=Real.log_le_log (Real.log_pos hk) logs
  rw [Real.log_mul (by norm_num) (Real.log_pos hp).ne'] at small
  norm_num only [Nat.cast_ofNat] at small
  have warm':1≤Real.log (H f):=by simpa using Real.log_le_log (Real.exp_pos 1) warm
  have second:=Real.log_nonneg warm'
  have cap:Real.log 2≤1:=by have h:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2);norm_num at h;exact h
  unfold scale
  rw [max_eq_right second]
  have height:max 0 (Real.log (Real.log (H K)))≤1+Real.log (Real.log (H f)):=max_le (by linarith) (by linarith)
  linarith

end YM.Integration.WilsonOriginalAlternativeTrialScales
end
