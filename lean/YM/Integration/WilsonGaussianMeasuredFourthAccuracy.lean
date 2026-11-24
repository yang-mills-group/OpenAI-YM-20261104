import YM.Integration.WilsonGaussianMeasuredFourthRay

/-! On a sufficiently late date, four powers of the physical fine coupling finance any
prescribed positive tolerance. The bound is purchased before the fine cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianMeasuredFourthAccuracy
open Filter PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open MatchingLedger.Compass.Income Next.SectorChange
open scoped Topology

theorem fine {G : Gauge} (R : Run G) (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per : ℕ, m<N →
      coupling (R.family.path.rep N per (m+1)).beta ≤ ε := by
  let D := R.family.path.levels
  have hot := (WardBin.bell D simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [hot.eventually_ge_atTop ((2/ε)^2)] with m hm N per hN
  have hb := WardBin.hot D (m+1)
  have hr := (Real.le_sqrt (div_nonneg (by norm_num : (0:ℝ)≤2) hε.le) hb.le).2 hm
  have hp := Weather.into_band R.family R.makes (Nat.succ_le_of_lt hN) per
  calc coupling (R.family.path.rep N per (m+1)).beta ≤ 2*(Real.sqrt (D.clock.hatBeta (m+1)))⁻¹ := hp.2
       _ = 2/Real.sqrt (D.clock.hatBeta (m+1)) := (div_eq_mul_inv _ _).symm
       _ ≤ ε := (div_le_iff₀ (Real.sqrt_pos.2 hb)).2 (by
         have h := (div_le_iff₀ hε).1 hr
         linarith only [h, mul_comm ε (Real.sqrt (D.clock.hatBeta (m+1)))])

theorem coefficient {g ε U : ℝ} {n p : ℕ} (hg : 0 ≤ g) (h₁ : g ≤ 1) (hε : g ≤ ε)
    (hp : p ≤ n) (hU : 0 ≤ U) : g^4*(g^n*U) ≤ ε*g^p*U := by
  have h₄ := (pow_le_pow_of_le_one hg h₁ (by norm_num : 1 ≤ 4)).trans (by simpa only [pow_one] using hε)
  have hn := pow_le_pow_of_le_one hg h₁ hp
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul h₄ hn (pow_nonneg hg _) (hg.trans hε)) hU

end YM.Integration.WilsonGaussianMeasuredFourthAccuracy
