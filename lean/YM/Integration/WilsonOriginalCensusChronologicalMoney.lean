import YM.Integration.WilsonOriginalDatedFieldsAtBoard

/-! Coupling and source expenses for a freshly posted ordinary census on consecutive original dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusChronologicalMoney
open Filter Finset PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonOriginalDatedFieldsAtBoard WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "g" N:max per:max j:max => regulatorRun R.family N per j

include simple in
theorem thermal : ∀ᶠ b:ℕ in atTop, ∀{i N per:ℕ}, b ≤ i → i ≤ N →
    0 < g N per i ∧ g N per i ≤ 1/2:=by
  obtain ⟨a,paid⟩:=eventually_atTop.1 (WilsonOriginalOpticalCouplingBand.cold R simple 2)
  filter_upwards [eventually_ge_atTop a] with b late
  intro i N per bi live
  have h0:0 < H i:=zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  have band:(H i)/2 ≤ R.family.path.β N per i:=(R.makes.wilson.represents N per i live).band.1
  have p:0 < g N per i:=inv_pos.mpr (Real.sqrt_pos.2 (by linarith only [h0,band]))
  have cash:=mul_le_mul_of_nonneg_right (paid i (late.trans bi) N per live) p.le
  rw [inv_mul_cancel₀ p.ne'] at cash
  exact ⟨p,by linarith only [cash]⟩

theorem cooled {x:ℝ}(pos:0 ≤ x)(small:x ≤ 1/2)(k:ℕ): (1+1)*x^(k+1) ≤ 1:=by
  have p:x^k  ≤  1:=pow_le_one₀ pos (by linarith only [small])
  have h:=mul_le_mul_of_nonneg_right p pos
  rw [one_mul] at h
  rw [pow_succ]
  linarith only [small,h]

include simple in
theorem fare {N per i:ℕ}(C:ℝ)(cc:0 ≤ C){e f:ℕ}(d:Degree)(he:e ≤ d.clock)(hf:f ≤ d.inverse)
    (gp:0 < g N per i)(gs:g N per i ≤ 1):
    C*(H i)^e*((g N per i)⁻¹)^f  ≤  pound R d C N per (i+1) i:=by
  have h₀:1 ≤ H i:=(R.family.path.levels.fits.delayed i).le
  have h₁:H i ≤ H (i+1):=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le (Nat.le_succ i)
  have h:(H i)^e ≤ (H (i+1))^d.clock:=(pow_le_pow_right₀ h₀ he).trans (pow_le_pow_left₀ (zero_le_one.trans h₀) h₁ _)
  have g₁:1 ≤ (g N per i)⁻¹:=(one_le_inv₀ gp).mpr gs
  exact mul_le_mul (mul_le_mul_of_nonneg_left h cc) (pow_le_pow_right₀ g₁ hf)
    (pow_nonneg (inv_nonneg.mpr gp.le) _) (mul_nonneg cc (pow_nonneg (zero_le_one.trans (h₀.trans h₁)) _))

end YM.Integration.WilsonOriginalCensusChronologicalMoney
end
