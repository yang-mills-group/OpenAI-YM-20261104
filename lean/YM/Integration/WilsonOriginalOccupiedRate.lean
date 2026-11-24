import YM.Integration.WilsonOriginalOccupiedClock
import YM.Integration.WilsonOriginalOccupiedWallet
import YM.Integration.WilsonOlderSignedOneMarkRate
import YM.Integration.WilsonJointAxialClock

/-! The authentic flat hard allowance refunds the radius, polynomial test restoration and fixed-order collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedRate
open Filter Finset Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Advent PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato ActualRunKernelPackets Pressure ConnectedActivityE6 Pert.Asymptotics
open Push.Local WilsonThermometerMixedCollarSubpower WilsonOriginalOccupiedWallet WilsonOriginalOccupiedStencil
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "κ" i:max => LocalComparison.forcedDivisor R.family i

include simple in
private theorem allowance (p a:ℕ){e:ℝ}(ep:0<e):
    ∀ᶠ t:ℕ in atTop,∀N per,t ≤ N → κ t*(H t)^a ≤ e*(regulatorRun R.family N per t)^p:=by
  filter_upwards [WilsonOlderSignedOneMarkRate.paid R simple a p (C:=1) (by norm_num) ep] with t pay N per top
  let B:=R.family.path.levels.budget t
  have w:1 ≤ hitWidth B:=by
    unfold hitWidth
    exact_mod_cast (one_le_pow₀ (show 1 ≤ B.B+B.B+1 by omega):1 ≤ (B.B+B.B+1)^4)
  have kp:0<κ t:=Real.sqrt_pos.2 (Real.exp_pos _)
  have sq:R.family.path.levels.clock.forcedAllowance t=(κ t)^2:=(Real.sq_sqrt (Real.exp_pos _).le).symm
  have bp:0<H t:=zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  have pp:=pay N per top t le_rfl ((H t)^a) (pow_nonneg bp.le _) (by simp)
  calc κ t*(H t)^a ≤ hitWidth B*(κ t*(H t)^a):=le_mul_of_one_le_left (mul_nonneg kp.le (pow_nonneg bp.le _)) w
       _=(hitWidth B*R.family.path.levels.clock.forcedAllowance t)*(H t)^a/κ t:=by
         rw [sq];field_simp
       _ ≤ _:=pp

include simple in
theorem original (n d a p:ℕ)(C:ℝ)(c0:0 ≤ C)(e:ℝ)(ep:0<e):
    ∀ᶠ f:ℕ in atTop,∀N per,f+1 ≤ N → ∀l:ℕ,
      (l:ℝ) ≤ C*(scale (H (f+1)))^d →
      inverseAmplitude n (κ (f+1)) ≤ 1 ∧
      (H (f+1))^a*Real.exp (n*(l:ℝ)*(scale (H (f+1)))^3)*
        (inverseAmplitude n (κ (f+1))*price n) ≤ e*(regulatorRun R.family N per (f+1))^p:=by
  let K:=1+4*(n:ℝ)*(price n+1)
  have pr:0 ≤ price n:=by unfold price; exact sum_nonneg fun i _=>sum_nonneg fun j _=>norm_nonneg _
  have k1:1 ≤ K:= le_add_of_nonneg_right (by positivity:0≤4*(n:ℝ)*(price n+1))
  have kp:0<K:=zero_lt_one.trans_le k1
  have c1:4*(n:ℝ) ≤ K:=by dsimp [K];nlinarith only [mul_nonneg (Nat.cast_nonneg n) pr]
  have c2:4*(n:ℝ)*price n ≤ K:=by dsimp [K];nlinarith only [show (0:ℝ)≤n from Nat.cast_nonneg n]
  have small:= (tendsto_add_atTop_nat 1).eventually (allowance R simple 0 0 (inv_pos.2 kp))
  have enough:=(tendsto_add_atTop_nat 1).eventually (allowance R simple (p+1) a (div_pos ep kp))
  filter_upwards [small,enough,WilsonThermometerMixedCollarSubpower.original R simple ((n:ℝ)*C)
    (mul_nonneg (Nat.cast_nonneg n) c0) d] with f startup paid clock N per top l span
  let g:=regulatorRun R.family N per (f+1)
  let z:=scale (H (f+1))
  let E:=Real.exp (n*(l:ℝ)*z^3)
  have gp:0<g:=ActualRunKernelPackets.regulator_pos R N per (f+1) top
  have z0:0 ≤ z:=by dsimp [z,scale];linarith only [le_max_left 0 (Real.log (Real.log (H (f+1))))]
  have l0:0 ≤ (n:ℝ)*l*z^3:=by positivity
  have date:=clock N top per ((n:ℝ)*l)
    (show (n:ℝ)*l ≤ ((n:ℝ)*C)*z^d by rw [mul_assoc];exact mul_le_mul_of_nonneg_left span (Nat.cast_nonneg n))
  have rent:g*E ≤ 1:=(mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
    (show (n:ℝ)*l*z^3 ≤ 3*((n:ℝ)*l)*z^3 by linarith only [l0])) gp.le).trans date
  have k0:0 ≤ κ (f+1):=(Real.sqrt_nonneg _)
  have init:=startup N per top
  simp only [pow_zero,mul_one] at init
  have inq:inverseAmplitude n (κ (f+1)) ≤ 1:=by
    calc _ ≤ K*κ (f+1):=mul_le_mul_of_nonneg_right c1 k0
         _ ≤ K*K⁻¹:=mul_le_mul_of_nonneg_left init kp.le
         _=1:=mul_inv_cancel₀ kp.ne'
  refine ⟨inq,?_⟩
  have h:=paid N per top
  change κ (f+1)*(H (f+1))^a ≤ e/K*g^(p+1) at h
  change (H (f+1))^a*E*(4*n*κ (f+1)*price n) ≤ e*g^p
  have bp:0 ≤ H (f+1):=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  calc _=(4*n*price n)*(κ (f+1)*(H (f+1))^a)*E:=by ring
       _ ≤ K*(e/K*g^(p+1))*E:=mul_le_mul_of_nonneg_right
         (mul_le_mul c2 h (mul_nonneg k0 (pow_nonneg bp _)) kp.le) (Real.exp_pos _).le
       _ = e*g^p*(g*E):=by rw [pow_succ];field_simp
       _ ≤ e*g^p*1:=mul_le_mul_of_nonneg_left rent (mul_nonneg ep.le (pow_nonneg gp.le _))
       _ = _:=mul_one _

end YM.Integration.WilsonOriginalOccupiedRate
