import YM.Integration.WilsonOriginalOpticalCouplingBand
import YM.Integration.WilsonReflectedRelativeDate

/-! Transfer an aperture quoted in the later original heat to the actual earlier station of the row. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryMasterEarlierHeat
open Function Filter Lattice RG Wilson PhysicalNext PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "a" j:max => R.family.S.a j

include simple in
theorem original (C:ℝ)(nonneg:0≤C)(u:ℕ):
    ∀ᶠj:ℕ in atTop,∀{f K:ℕ},j≤f→f≤K→a j/a K≤C*(H f)^u →
      H f≤2*H j ∧ a j/a K≤(H j)^(u+1):=by
  let s:=G.slopeConstant*((u+1:ℕ):ℝ)
  have sn:0 ≤ s:=mul_nonneg (Gauge.slopeConstant_pos simple).le (by positivity)
  have late:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [late.eventually_ge_atTop C,late.eventually_ge_atTop ((4*s)^2),
    late.eventually_ge_atTop (C*2^u)] with j large root cap
  intro f K jf fk span
  have mono:H j≤H f:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le jf
  have hn:0≤H f:=zero_le_one.trans (R.family.path.levels.fits.delayed f).le
  have sq:4*s≤Real.sqrt (H f):=Real.le_sqrt_of_sq_le (root.trans mono)
  have logf:Real.log (H f)≤2*Real.sqrt (H f):=calc
    Real.log (H f)=Real.log ((Real.sqrt (H f))^2):=by rw [Real.sq_sqrt hn]
    _=2*Real.log (Real.sqrt (H f)):=by rw [Real.log_pow];norm_num
    _≤2*Real.sqrt (H f):=mul_le_mul_of_nonneg_left (Real.log_le_self (Real.sqrt_nonneg _)) (by norm_num)
  have absorb:2*(s*Real.log (H f))≤H f:=calc
    _≤2*(s*(2*Real.sqrt (H f))):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left logf sn) (by norm_num)
    _=(4*s)*Real.sqrt (H f):=by ring
    _≤Real.sqrt (H f)*Real.sqrt (H f):=mul_le_mul_of_nonneg_right sq (Real.sqrt_nonneg _)
    _=H f:=Real.mul_self_sqrt hn
  have upper:a j/a K≤(H f)^(u+1):=calc
    _≤C*(H f)^u:=span
    _≤(H f)*(H f)^u:=mul_le_mul_of_nonneg_right (large.trans mono) (pow_nonneg hn _)
    _=(H f)^(u+1):=by rw [pow_succ];ring
  have recorded:=Real.log_le_log (div_pos (R.family.S.a_pos j) (R.family.S.a_pos K)) upper
  rw [WilsonReflectedRelativeDate.ratio,Real.log_pow] at recorded
  have slope:=WilsonReflectedRelativeDate.monotone R fk
  have change:H f-H j=G.slopeConstant*(R.family.S.scale f-R.family.S.scale j):=by
    change (_+G.slopeConstant*R.family.S.scale f)-(_+G.slopeConstant*R.family.S.scale j)=_
    ring
  have small:H f-H j ≤ s*Real.log (H f):=calc
    _=G.slopeConstant*(R.family.S.scale f-R.family.S.scale j):=change
    _≤G.slopeConstant*((u+1:ℕ)*Real.log (H f)):=
      mul_le_mul_of_nonneg_left (le_trans (sub_le_sub_right slope _) recorded) (Gauge.slopeConstant_pos simple).le
    _=s*Real.log (H f):=by dsimp only [s]; ring
  have both:H f≤2*H j:=by linarith only [small,absorb]
  refine ⟨both,span.trans ?_⟩
  calc
    C*(H f)^u≤C*(2*H j)^u:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn both _) nonneg
    _=(C*2^u)*(H j)^u:=by rw [mul_pow];ring
    _≤(H j)*(H j)^u:=mul_le_mul_of_nonneg_right cap (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed j).le) _)
    _=(H j)^(u+1):=by rw [pow_succ];ring

end YM.Integration.WilsonCapturedPrimaryMasterEarlierHeat
end
