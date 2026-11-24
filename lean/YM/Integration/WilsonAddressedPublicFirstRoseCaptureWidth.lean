import YM.Integration.WilsonMovingForkOpticalStops
import YM.Integration.WilsonCloseCaptureDate

/-! The two actual single-block overshoots at compact capture and at the
predecessor of the infrared ear have fixed optical costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstRoseCaptureWidth
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale
local notation "a" => R.family.S.a

include simple slow in
theorem block {c j:ℕ}(before:c≤j):((R.family.S.block c).val:ℝ) ≤ 3*H j:=by
  have cp:1 ≤ H c:=(R.family.path.levels.fits.delayed c).le
  have lpos:0 ≤ 2+Real.log (H c):=by linarith only [Real.log_nonneg cp]
  have coarse:((R.family.S.block c).val:ℝ) ≤ Real.log (2+Real.log (H c)):=slow.2 c
  have link:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le before
  linarith only [coarse,Real.log_le_self lpos,Real.log_le_self (zero_le_one.trans cp),link,cp]

include simple slow in
theorem original {j c B:ℕ}{r M:ℝ}(rp:0<r)(mp:0<M)(before:c≤j)
    (openFace:a (c+1) < M*r)(heat:3*M ≤ H j)(posted:r ≤ (H j)^B*a j):
    a c/a j ≤ (H j)^(B+2):=by
  have cp:0 ≤ H j:=(zero_lt_one.trans (R.family.path.levels.fits.delayed j)).le
  have step:a c=((R.family.S.block c).val:ℝ)*a (c+1):=by
    rw [R.family.S.a_step,mul_div_cancel₀ _ (by exact_mod_cast (R.family.S.block c).property.ne')]
  have bought:((R.family.S.block c).val:ℝ)*M ≤ (H j)^2:=by
    calc _ ≤ (3*H j)*M:=mul_le_mul_of_nonneg_right (block R simple slow before) mp.le
         _ = (H j)*(3*M):=by ring
         _ ≤ _:=by simpa only [pow_two] using mul_le_mul_of_nonneg_left heat cp
  rw [div_le_iff₀ (R.family.S.a_pos j),step]
  calc _ ≤ ((R.family.S.block c).val:ℝ)*(M*r):=mul_le_mul_of_nonneg_left openFace.le (Nat.cast_nonneg _)
       _ ≤ (H j)^2*r:=by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right bought rp.le
       _ ≤ (H j)^2*((H j)^B*a j):=mul_le_mul_of_nonneg_left posted (sq_nonneg _)
       _ = _:=by rw [pow_add];ring

include simple slow in
theorem previous (first K width:ℕ)(priced:a (first+1)/a K ≤ H (first+1)^width):
    σ K-σ first ≤ ((width+2:ℕ):ℝ)*(1+Real.log (H (first+1))):=by
  have hp:0 < H (first+1):=zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  have lg:0 ≤ Real.log (H (first+1)):=Real.log_nonneg (R.family.path.levels.fits.delayed _).le
  have whole:=Real.log_le_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) priced
  rw [WilsonReflectedRelativeDate.ratio R,Real.log_pow] at whole
  have close:=Real.log_le_log (show 0<((R.family.S.block first).val:ℝ) by
    exact_mod_cast (R.family.S.block first).property) (block R simple slow (Nat.le_succ first))
  rw [Real.log_mul (by norm_num) hp.ne'] at close
  have small:Real.log 3 ≤ 2:=by
    simpa only [show (3:ℝ)-1=2 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num:0<(3:ℝ))
  rw [R.family.S.scale_succ] at whole
  push_cast
  linarith only [whole,close,small,lg,Nat.cast_nonneg (α:=ℝ) width]

end YM.Integration.WilsonAddressedPublicFirstRoseCaptureWidth
end
