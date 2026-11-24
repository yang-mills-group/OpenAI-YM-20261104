import YM.Integration.WilsonOriginalOccupiedOpticalHeat

/-! The original divided hard bill after an optical interval, uniformly in both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedOpticalRate
open Filter Finset Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Advent PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato ActualRunKernelPackets Pressure ConnectedActivityE6 Pert.Asymptotics
open Push.Local WilsonThermometerMixedCollarSubpower WilsonOriginalOccupiedWallet WilsonOriginalOccupiedStencil
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "κ" i:max => LocalComparison.forcedDivisor R.family i

open private YM.Integration.WilsonOriginalOccupiedRate.allowance from YM.Integration.WilsonOriginalOccupiedRate
include simple in
theorem original (n d a p:ℕ)(C:ℝ)(c0:0 ≤ C)(e:ℝ)(ep:0<e):
    ∀ᶠ f:ℕ in atTop,∀N per,f+1 ≤ N → ∀l:ℕ,
      (l:ℝ) ≤ C*(1+Real.log (H (f+1)))^d →
      inverseAmplitude n (κ (f+1)) ≤ 1 ∧
      (H (f+1))^a*Real.exp (n*(l:ℝ)*(scale (H (f+1)))^3)*
        (inverseAmplitude n (κ (f+1))*price n) ≤ e*(regulatorRun R.family N per (f+1))^p:=by
  let K:=1+4*(n:ℝ)*(price n+1)
  have pr:0 ≤ price n:=by unfold price; exact sum_nonneg fun i _=>sum_nonneg fun j _=>norm_nonneg _
  have k1:1 ≤ K:= le_add_of_nonneg_right (by positivity:0≤4*(n:ℝ)*(price n+1))
  have kp:0<K:=zero_lt_one.trans_le k1
  have c1:4*(n:ℝ) ≤ K:=by dsimp [K];nlinarith only [mul_nonneg (Nat.cast_nonneg n) pr]
  have c2:4*(n:ℝ)*price n ≤ K:=by dsimp [K];nlinarith only [show (0:ℝ)≤n from Nat.cast_nonneg n]

  have small:=(tendsto_add_atTop_nat 1).eventually
    (YM.Integration.WilsonOriginalOccupiedRate.allowance R simple 0 0 (inv_pos.2 kp))
  have m0:0<e/K:=div_pos ep kp
  have enough:=(tendsto_add_atTop_nat 1).eventually
    (YM.Integration.WilsonOriginalOccupiedRate.allowance R simple (p*2) (a*2) (sq_pos_of_pos m0))
  have heated:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [small,enough,heated.eventually (WilsonOriginalOccupiedOpticalHeat.original n d C c0)] with
    f startup paid optical N per top l span
  let g:=regulatorRun R.family N per (f+1)
  let h:=H (f+1)
  let E:=Real.exp (n*(l:ℝ)*(scale h)^3)
  let k:=κ (f+1)
  have g0:0 ≤ g:=(ActualRunKernelPackets.regulator_pos R N per (f+1) top).le
  have h0:0 ≤ h:=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have k0:0 ≤ k:=Real.sqrt_nonneg _
  have ek:E*Real.sqrt k ≤ 1:=optical l span
  have init:=startup N per top
  simp only [pow_zero,mul_one] at init
  have inq:inverseAmplitude n k ≤ 1:=by
    calc _ ≤ K*k:=mul_le_mul_of_nonneg_right c1 k0
         _ ≤ K*K⁻¹:=mul_le_mul_of_nonneg_left init kp.le
         _=1:=mul_inv_cancel₀ kp.ne'
  refine ⟨inq,?_⟩
  have hpaid:=paid N per top
  change k*h^(a*2) ≤ (e/K)^2*g^(p*2) at hpaid
  have sq:(Real.sqrt k*h^a)^2 ≤ (e/K*g^p)^2:=by
    simpa only [mul_pow,Real.sq_sqrt k0,pow_mul] using hpaid
  have single:Real.sqrt k*h^a ≤ e/K*g^p:=(sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg h0 _))
    (mul_nonneg m0.le (pow_nonneg g0 _))).1 sq
  change h^a*E*(4*n*k*price n) ≤ e*g^p
  calc _=(4*n*price n)*((Real.sqrt k)^2*h^a)*E:=by rw [Real.sq_sqrt k0];ring
       _=(4*n*price n)*(Real.sqrt k*h^a)*(E*Real.sqrt k):=by ring
       _ ≤ K*(e/K*g^p)*1:=mul_le_mul
         (mul_le_mul c2 single (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg h0 _)) kp.le) ek
         (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
         (mul_nonneg kp.le (mul_nonneg m0.le (pow_nonneg g0 _)))
       _ = e*g^p:=by field_simp

end YM.Integration.WilsonOriginalOccupiedOpticalRate
