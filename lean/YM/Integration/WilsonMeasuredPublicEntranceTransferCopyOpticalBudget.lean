import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyAwardPrice
import YM.Integration.WilsonMeasuredPublicEntranceMeshClock

/-! Optical restoration of all terminal widths for a fixed finite family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyOpticalBudget
open Filter Real
open scoped Topology

/-- At most logarithmically many two-Hat factors and finitely many grouped
fields are affordable in the actual height-zero allowance. -/
theorem original (σ A E:ℝ) (s0:0<σ) (a0:0≤A) (e0:0≤E) (p n:ℕ) :
    ∀ᶠ H:ℝ in atTop, ∀ m:ℕ,(m:ℝ)≤A*(1+log H) →
      7*(4*H)^2*(E*H^p*(4*H^2)^m)^n≤exp (H/(10*σ)):=by
  let D:ℝ:=3+((p:ℝ)+1)*(n:ℝ)+6*A*(n:ℝ)
  have d0:0<D:=by dsimp [D];positivity
  have rate:0<(10*σ*D)⁻¹:=by positivity
  have tiny:=(isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).def rate
  filter_upwards [tiny,tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (112:ℝ),
    eventually_ge_atTop E] with H small one high ample m num
  have hp:0<H:=by linarith only [high]
  have lp:=zero_le_one.trans one
  have n0:0≤(n:ℝ):=by positivity
  have p0:0≤(p:ℝ):=by positivity
  have cut:(m:ℝ)≤2*A*log H:=by nlinarith only [num,mul_nonneg a0 (sub_nonneg.mpr one)]
  have left:7*(4*H)^2≤H^3:=by nlinarith only [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr high)]
  have inside:E*H^p≤H^(p+1):=by simpa [pow_succ,mul_comm] using mul_le_mul_of_nonneg_right ample (pow_nonneg hp.le p)
  have bit:4*H^2≤H^3:=by nlinarith only [mul_nonneg (sq_nonneg H) (show 0≤H-4 by linarith only [high])]
  have tile:E*H^p*(4*H^2)^m≤H^(p+1)*(H^3)^m:=
    mul_le_mul inside (pow_le_pow_left₀ (by positivity) bit m) (by positivity) (by positivity)
  let θ:=3+(p+1+3*m)*n
  have sheet:7*(4*H)^2*(E*H^p*(4*H^2)^m)^n≤H^θ:=by
    calc
      _≤H^3*(H^(p+1)*(H^3)^m)^n:=
        mul_le_mul left (pow_le_pow_left₀ (by positivity) tile n) (by positivity) (by positivity)
      _=_:=by dsimp only [θ];rw [pow_add H 3 ((p+1+3*m)*n),pow_mul H (p+1+3*m) n,pow_add H (p+1) (3*m),pow_mul H 3 m]
  have cost:(θ:ℝ)≤D*log H:=by
    dsimp only [D,θ];push_cast
    nlinarith only [one,mul_le_mul_of_nonneg_right cut n0,
      mul_nonneg (sub_nonneg.mpr one) (mul_nonneg (by linarith only [p0]:0≤(p:ℝ)+1) n0)]
  have paid:(log H)^2≤(10*σ*D)⁻¹*H:=by
    simpa [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg hp.le] using small
  have total:D*(log H)^2≤H/(10*σ):=by
    apply (mul_le_mul_of_nonneg_left paid d0.le).trans_eq
    field_simp
  calc
    _≤H^θ:=sheet
    _=exp (log (H^θ)):=(Real.exp_log (pow_pos hp _)).symm
    _≤_:=by
      apply Real.exp_le_exp.mpr
      rw [Real.log_pow]
      exact (mul_le_mul_of_nonneg_right cost lp).trans ((by ring : D*log H*log H=D*(log H)^2).le.trans total)

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyOpticalBudget
