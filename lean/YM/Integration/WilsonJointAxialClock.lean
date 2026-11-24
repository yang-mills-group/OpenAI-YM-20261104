import YM.Integration.WilsonVacuumPreResetSameTime

/-! Cashing finite-order estimates in the coupling of the actual upper step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonJointAxialClock
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics PhysicalNext.Repeat.Legato
open AnalyticBridge VerifiedReset RG01Estimate WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonLimitConstruction
open scoped Topology
variable {G : Gauge}

theorem original (R : Run G) (simple : G.Simple) :
    ∀ᶠ i : ℕ in atTop, ∀ N per : ℕ, i<N →
      let g := regulatorRun R.family N per (i+1)
      0 < g ∧ g ≤ 1 ∧ regulatorRun R.family N per i ≤ 3*g ∧
        (R.family.path.levels.clock.hatBeta i)⁻¹ ≤ 4*g^2 := by
  let V:=R.family.path.levels
  have warm := ((Next.Rank.Station.hat_rate V simple).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 2
  filter_upwards [warm,RG01.Physical.nextHat simple V,WilsonVacuumPreResetSameTime.ratios R simple] with i high grow ratios N per cut
  let b:ℝ := (R.family.path.rep N per (i+1)).beta
  let x:ℝ := V.clock.hatBeta i
  change 2 ≤ V.clock.hatBeta (i+1) at high
  change V.clock.hatBeta (i+1) ≤ 2*x at grow
  have lower : V.clock.hatBeta (i+1)/2 ≤ b := (R.makes.wilson.represents N per (i+1) cut).band.1
  have upper : b ≤ 2*V.clock.hatBeta (i+1) := (R.makes.wilson.represents N per (i+1) cut).band.2
  have b1 : 1 ≤ b := by linarith only [high,lower]
  have b0 : 0 < b := zero_lt_one.trans_le b1
  have x0 : 0 < x := zero_lt_one.trans (V.fits.delayed i)
  have root : 1 ≤ Real.sqrt b := by simpa using Real.sqrt_le_sqrt b1
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr b0),inv_le_one_of_one_le₀ root,ratios N per cut,?_⟩
  change x⁻¹ ≤ 4*(Real.sqrt b)⁻¹^2
  rw [inv_pow,Real.sq_sqrt b0.le,← div_eq_mul_inv,←one_div]
  exact (div_le_div_iff₀ x0 b0).2 (by linarith only [grow,upper])

theorem accuracy {x g ε : ℝ} (gp : 0<g) (small : g≤1) (xp : 0≤x) (rel : x≤3*g)
    (q order : ℕ) (extra : q≤order) (ep : 0≤ε) (fraction : ε*((3:ℝ)^q+2)≤1) :
    ε*x^q + ε*g^order + ε*g^q ≤ g^q := by
  calc
    _ ≤ ε*(3*g)^q+ε*g^q+ε*g^q :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ xp rel _) ep)
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le small extra) ep)) le_rfl
    _ = (ε*((3:ℝ)^q+2))*g^q := by rw [mul_pow]; ring
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right fraction (pow_nonneg gp.le q)

theorem exceptional {x g : ℝ} (xp : 0≤x) (gp : 0≤g) (small : g≤1) (refund : x ≤ 4*g^2) (K : ℕ) :
    x^K ≤ (4:ℝ)^K*g^K := by
  calc
    _ ≤ (4*g^2)^K := pow_le_pow_left₀ xp refund _
    _ = (4:ℝ)^K*g^(2*K) := by rw [mul_pow,pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp small (by omega)) (by positivity)

end YM.Integration.WilsonJointAxialClock
