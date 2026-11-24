import YM.QuadraticLocal.View
import YM.Integration.WilsonMovingMentorMarkedRate

/-! The actual stage exponent in a registered salary can pay any fixed
number of occupied factors, uniformly before cutoff and period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorPageReserve
open Filter RG PhysicalNext.Repeat.Legato QuadraticLocal
open scoped Topology

theorem powers {G : Gauge} (R : Run G) (simple : G.Simple) (h : ℕ) {δ : ℝ} (positive : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ v : ℝ, 0 ≤ v →
      v ≤ (R.alloy.B.a.clock.hatBeta (m+1))^(Beaming.grain (R.alloy.B.a.clock.J m)) →
        v^h ≤ (R.alloy.B.a.clock.hatBeta (m+1))^δ := by
  obtain ⟨d,high⟩ := exists_nat_gt ((h:ℝ)/δ)
  obtain ⟨start,warm⟩ := eventually_atTop.1
    ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_ge_atTop start,R.alloy.B.a.fits.deep.eventually_ge_atTop d] with m late deep v vp charged
  let b := R.alloy.B.a.clock.hatBeta (m+1)
  let j := R.alloy.B.a.clock.J m
  have hot : 1 ≤ b := warm (m+1) (by omega)
  have floor : (d:ℝ) ≤ j := by exact_mod_cast deep
  have room : 0 < (j:ℝ)+1 := by positivity
  have cap : (h:ℝ)/((j:ℝ)+1) ≤ δ := (div_le_iff₀ room).mpr (by
    have lower := (div_lt_iff₀ positive).mp high
    nlinarith)
  have exponent : Beaming.grain j*(h:ℝ) ≤ δ := by
    convert cap using 1
    simp only [Beaming.grain,div_eq_mul_inv,one_mul]
    ring
  calc
    v^h ≤ (b^(Beaming.grain j))^h := pow_le_pow_left₀ vp charged h
    _ = b^(Beaming.grain j*(h:ℝ)) := by rw [Real.rpow_mul (zero_le_one.trans hot),Real.rpow_natCast]
    _ ≤ b^δ := Real.rpow_le_rpow_of_exponent_le hot exponent

end YM.Integration.WilsonMovingMentorPageReserve
end
