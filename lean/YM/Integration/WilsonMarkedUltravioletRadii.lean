import YM.Integration.WilsonConditionalTaylorWheelShortClock
import YM.Integration.WilsonMeasuredWindow

/-! The true first mesh stop finances every later local logarithmic support tariff, without comparing the two endpoint temperatures. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedUltravioletRadii
open Filter Set Real RG Wilson Lattice OPE
open PhysicalNext.Repeat.Legato WilsonMeasuredAdmission
open scoped Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "A" => R.family.path.levels
local notation "H" => R.family.path.levels.clock.hatBeta

include simple in
theorem increasing_room (B:ℕ)(B0:0 < B):
    ∀ᶠ m:ℕ in atTop,∀i:ℕ,m ≤ i →
      R.family.S.a i*(mast A i)^B ≤ R.family.S.a m*(mast A m)^B:=by
  have hot:=Next.Rank.Station.hat_rate A simple
  filter_upwards [hot.eventually_ge_atTop (G.slopeConstant*(B:ℝ))] with m funded i mi
  let d:=R.family.S.scale i-R.family.S.scale m
  have d0:0 ≤ d:=sub_nonneg.mpr ((OPE.scale_mono R.family.S).monotone mi)
  have hm:0 < H m:=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have hi:0 < H i:=zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  have bp:0 < (B:ℝ):=by exact_mod_cast B0
  have af:H i-H m=G.slopeConstant*d:=WilsonConditionalTaylorWheelShortClock.affine R m i
  have logcost:=Real.log_le_sub_one_of_pos (div_pos hi hm)
  rw [Real.log_div hi.ne' hm.ne'] at logcost
  have cash: G.slopeConstant/(H m) ≤ 1/(B:ℝ):=by
    apply (div_le_div_iff₀ hm bp).mpr
    simpa using funded
  have slope: H i/H m-1=(G.slopeConstant/H m)*d:=by
    field_simp
    linarith only [af]
  have step:Real.log (H i)-Real.log (H m) ≤ d/(B:ℝ):=calc
    _ ≤ H i/H m-1:=logcost
    _=(G.slopeConstant/H m)*d:=slope
    _ ≤ (1/(B:ℝ))*d:=mul_le_mul_of_nonneg_right cash d0
    _=d/(B:ℝ):=by ring
  have xp:0 ≤ d/(B:ℝ):=div_nonneg d0 bp.le
  have tall:1 ≤ mast A m:=(mast_gt_one A m).le
  have bound:mast A i ≤ mast A m*exp (d/(B:ℝ)):=calc
    _ ≤ mast A m+d/(B:ℝ):=by unfold mast WilsonAdmissionScale.logarithm;linarith only [step]
    _ ≤ mast A m*(1+d/(B:ℝ)):=by nlinarith only [mul_nonneg (sub_nonneg.mpr tall) xp]
    _ ≤ _:=mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (d/(B:ℝ))]) (mast_pos A m).le
  have ratio:exp d=R.family.S.a m/R.family.S.a i:=by
    have unit(t:ℕ):exp (R.family.S.scale t)=(R.family.S.a t)⁻¹:=Real.exp_log (inv_pos.mpr (R.family.S.a_pos t))
    rw [show d=R.family.S.scale i-R.family.S.scale m by rfl,Real.exp_sub,unit,unit]
    field_simp [(R.family.S.a_pos m).ne',(R.family.S.a_pos i).ne']
  have exponent:(B:ℝ)*(d/(B:ℝ))=d:=by field_simp
  calc
    _ ≤ R.family.S.a i*(mast A m*exp (d/(B:ℝ)))^B:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mast_pos A i).le bound B) (R.family.S.a_pos i).le
    _=R.family.S.a m*(mast A m)^B:=by
      rw [mul_pow,←Real.exp_nat_mul,exponent,ratio]
      field_simp [(R.family.S.a_pos i).ne']

theorem reserve (p:ℕ)(C:ℝ):
    ∀ᶠ r:ℝ in 𝓝[>]0,let m:=WilsonMeasuredWindow.stop A simple (p+1) r
      ∀ i:ℕ,m ≤ i → C*(mast A i)^p ≤ r/R.family.S.a i:=by
  have soft:∀ᶠ m:ℕ in atTop,C ≤ mast A m:=by
    filter_upwards [(WilsonAdmissionScale.logarithm_tendsto A simple).eventually_ge_atTop C] with m test
    unfold mast;linarith only [test]
  have stop:=WilsonMeasuredWindow.stop_tendsto A simple (p+1) (by omega)
  filter_upwards [stop.eventually ((increasing_room R simple (p+1) (by omega)).and soft),
    self_mem_nhdsWithin] with r stamp positive m i mi
  have rp:0 < r:=positive
  have turn:C ≤ mast A i:=stamp.2.trans (mast_monotone A simple mi)
  apply (le_div_iff₀ (R.family.S.a_pos i)).mpr
  calc
    _ ≤ (mast A i*(mast A i)^p)*R.family.S.a i:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right turn (pow_nonneg (mast_pos A i).le _)) (R.family.S.a_pos i).le
    _=R.family.S.a i*(mast A i)^(p+1):=by ring
    _ ≤ R.family.S.a m*(mast A m)^(p+1):=stamp.1 i mi
    _ ≤ r:=WilsonMeasuredWindow.stop_spec A simple (p+1) rp
end YM.Integration.WilsonMarkedUltravioletRadii
