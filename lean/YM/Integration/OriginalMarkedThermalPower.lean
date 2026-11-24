import YM.Integration.ActualOriginalQInitialInput
import YM.RG01.Slack

/-! The original thermal allowance absorbs any fixed coefficient in the
actual positive finite-cutoff regulator coupling, uniformly in the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedThermalPower
open Filter Lattice Wilson RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology

variable {G : Gauge} (R : Run G) (hG : G.Simple)

private theorem actual_beta {N p k : ℕ} (hk : k≤N) (a : ℕ) :
    ((R.family.path.levels.clock.hatBeta k)⁻¹)^a ≤ (2:ℝ)^a*(regulatorRun R.family N p k)^a := by
  let y := R.family.path.levels.clock.hatBeta k
  let β := (R.family.path.rep N p k).beta
  have hy : 1<y := R.family.path.levels.fits.delayed k
  have band := (R.makes.wilson.represents N p k hk).band
  have pos : 0<β := (div_pos (zero_lt_one.trans hy) (by norm_num)).trans_le band.1
  have upper : β≤2*y := band.2
  have root : Real.sqrt β≤2*y := by nlinarith [Real.sq_sqrt pos.le,sq_nonneg (Real.sqrt β-1)]
  have inverse : y⁻¹≤2*(Real.sqrt β)⁻¹ := by
    rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (zero_lt_one.trans hy) (Real.sqrt_pos.2 pos)]
    simpa only [one_mul] using root
  change (y⁻¹)^a≤(2:ℝ)^a*((Real.sqrt β)⁻¹)^a
  rw [←mul_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (zero_lt_one.trans hy).le) inverse _

include hG in
theorem actual (C : ℝ) {ε : ℝ} (hε : 0<ε) (a : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N p : ℕ), m<N →
      C*R.family.path.levels.clock.forcedAllowance (m+1) ≤
        ε*(regulatorRun R.family N p (m+1))^a := by
  let T := R.family.path.levels
  let A := |C|+1
  have Apos : 0<A := by dsimp [A]; positivity
  have factor : 0<(2:ℝ)^a := pow_pos (by norm_num) _
  let δ := ε/(A*(2:ℝ)^a)
  have δpos : 0<δ := div_pos hε (mul_pos Apos factor)
  obtain ⟨k,hk⟩ := eventually_atTop.1 ((RG01.Physical.shrink hG T a).eventually_lt_const δpos)
  filter_upwards [eventually_ge_atTop k] with m hm N p level
  let b := T.clock.hatBeta (m+1)
  let κ := T.clock.forcedAllowance (m+1)
  have bpos : 0<b := zero_lt_one.trans (T.fits.delayed _)
  have hit : κ≤δ*(b⁻¹)^a := by
    rw [inv_pow,←div_eq_mul_inv,le_div_iff₀ (pow_pos bpos a)]
    simpa only [mul_comm] using (hk (m+1) (hm.trans (Nat.le_succ m))).le
  have native := actual_beta R (N:=N) (p:=p) level a
  have ca : C≤A := (le_abs_self C).trans (by dsimp [A]; linarith)
  change C*κ≤_
  calc
    C*κ ≤ A*κ := mul_le_mul_of_nonneg_right ca (Real.exp_nonneg _)
    _ ≤ A*(δ*(b⁻¹)^a) := mul_le_mul_of_nonneg_left hit Apos.le
    _ ≤ A*(δ*((2:ℝ)^a*(regulatorRun R.family N p (m+1))^a)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left native δpos.le) Apos.le
    _ = _ := by
      have price : A*δ*(2:ℝ)^a=ε := by
        dsimp [δ]
        field_simp [Apos.ne',factor.ne']
      rw [←mul_assoc,←mul_assoc,price]

end YM.Integration.OriginalMarkedThermalPower
end
