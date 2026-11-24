import YM.Integration.WilsonMovingMentorHardTemperature

/-! The authentic registered refund for any fixed number of slots costs one physical coupling order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorPageCoupling
open Filter RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ConnectedActivityE6 QuadraticLocal
open scoped Topology

theorem repaid {G : Gauge} (R : Run G) (simple : G.Simple) (slots q : ℕ) {ε : ℝ} (positive : 0<ε) :
    ∀ᶠ m : ℕ in atTop, ∀ v : ℝ, 0 ≤ v →
      v ≤ (R.alloy.B.a.clock.hatBeta (m+1))^(Beaming.grain (R.alloy.B.a.clock.J m)) →
      ∀ N per : ℕ, m < N →
        let g := Coat.gStep (R.family.path.rep N per (m+1)).beta
        v^slots*g^(q+1) ≤ ε*g^q := by
  have grow := (Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  have vanishes := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp grow
  have room : 0 < ε^2/2 := by positivity
  filter_upwards [WilsonMovingMentorPageReserve.powers R simple (2*slots) (by norm_num : (0:ℝ)<1/2),
    vanishes.eventually_lt_const room,grow.eventually_gt_atTop (0:ℝ)] with m paid small warm v nonnegative bound N per period
  let b := R.alloy.B.a.clock.hatBeta (m+1)
  let g := Coat.gStep (R.family.path.rep N per (m+1)).beta
  change 0 < b at warm
  change b^(-((1:ℝ)/2)) < ε^2/2 at small
  have wage : v^(2*slots) ≤ (ε^2/2)*b := calc
    v^(2*slots) ≤ b^((1:ℝ)/2) := paid v nonnegative bound
    _ = b^(-((1:ℝ)/2)+1) := by norm_num
    _ = b^(-((1:ℝ)/2))*b := by rw [Real.rpow_add warm,Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right small.le warm.le
  have currency : g^2*b ≤ 2 := by
    simpa [g,b] using WilsonMovingMentorHardTemperature.measured R (Nat.succ_le_of_lt period) per 1 0
  have gp : 0≤g := by dsimp [g,Coat.gStep]; positivity
  have squared : (v^slots*g)^2 ≤ ε^2 := calc
    (v^slots*g)^2 = v^(2*slots)*g^2 := by rw [mul_pow,←pow_mul,Nat.mul_comm slots 2]
    _ ≤ ((ε^2/2)*b)*g^2 := mul_le_mul_of_nonneg_right wage (sq_nonneg g)
    _ = (ε^2/2)*(g^2*b) := by ring
    _ ≤ (ε^2/2)*2 := mul_le_mul_of_nonneg_left currency room.le
    _ = ε^2 := by ring
  have comparison : v^slots*g ≤ ε := (sq_le_sq₀ (mul_nonneg (pow_nonneg nonnegative slots) gp) positive.le).mp squared
  change v^slots*g^(q+1) ≤ ε*g^q
  calc
    v^slots*g^(q+1) = (v^slots*g)*g^q := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right comparison (pow_nonneg gp q)

end YM.Integration.WilsonMovingMentorPageCoupling
end
