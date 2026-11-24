import YM.Integration.WilsonTwoBirthCoverIncome
import YM.Integration.WilsonLimitConstruction.FundedPointSourceClock

/-! The actual marked carry over the one interval separating the two reporting
births costs a fixed power of the reporter's measured inverse-coupling schedule. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAdjacentWindingIncome
open Function Filter Lattice Wilson RG Marker Source Labels Precision Laurent
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos
open WilsonCoeffUV.StableStrip WilsonLimitConstruction WilsonLimitConstruction.FundedInheritedMarkedInput
open scoped Topology Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ}

theorem original (R : Run G) (simple : G.Simple) (K : ι → ℕ) (e : ℕ) :
    ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ᶠ m in atTop,
      ∀ (Q : Realm G (e+1) Credit.leanC), Q.anchor ≤ m → Q.draws = R.family.path.levels →
        Q.y = zz R.family.path.levels → ∀ b : ℝ, 0 ≤ b →
        WilsonTwoBirthCoverIncome.amount (m:=m) (D:=D) (k:=k) Q K b ≤
          C*(R.family.path.levels.clock.hatBeta m)^d*b := by
  let L := R.family.path.levels
  let T := tollStep G D k K e Credit.leanC Credit.leanC
  obtain ⟨U,hU,window⟩ := FundedPointSourceClock.clock R simple 1
  let c := G.slopeConstant
  have hc : 0 < c := G.slopeConstant_pos simple
  let M := L.clock.bar + c*U + 2*U + 1
  have hM : 0 < M := by dsimp [M]; positivity [L.clock.bar_pos]
  have hT : 0 ≤ T.x := zero_le_one.trans T.good
  refine ⟨T.x*M^T.d+1,T.d,by positivity,?_⟩
  filter_upwards [window,(WardBin.bell L simple).eventually_ge_atTop (Real.exp 1)] with m win before
  let H := L.clock.hatBeta m
  have h1 : 1 ≤ H := (Real.one_le_exp (by norm_num)).trans before
  have above := (WilsonStartup.Timing.hat_mono L hc.le) (Nat.le_succ m)
  have e₁ : Real.exp 1 ≤ L.clock.hatBeta (m+1) := before.trans above
  have logH : 1 ≤ Real.log (L.clock.hatBeta (m+1)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) e₁
  have y₁ : zz L (m+1) ≤ L.clock.hatBeta (m+1) := by
    change 1+Real.log (Real.log (L.clock.hatBeta (m+1))) ≤ _
    linarith [Real.log_le_self (show 0 ≤ Real.log (L.clock.hatBeta (m+1)) by linarith),
      Real.log_le_sub_one_of_pos (WardBin.hot L (m+1))]
  have u₁ : 1+|L.S.scale (m+1)| ≤ U*H := by simpa using win 0 (by omega)
  have u₂ : 1+|L.S.scale (m+2)| ≤ U*H := by simpa using win 1 le_rfl
  have hβ : L.clock.hatBeta (m+1) ≤ (L.clock.bar+c*U)*H := by
    change L.clock.bar+c*L.S.scale (m+1) ≤ _
    nlinarith [L.clock.bar_pos,le_abs_self (L.S.scale (m+1)),
      mul_nonneg L.clock.bar_pos.le (sub_nonneg.mpr h1),
      mul_nonneg hc.le (sub_nonneg.mpr ((by linarith : |L.S.scale (m+1)| ≤ U*H)))]
  intro Q hm same clock b hb
  have zpos : 1 ≤ horizon Q (m+1) (m+2) :=
    (Q.depth _ (hm.trans (Nat.le_succ _))).trans
      ((PadRank.frugal Q (hm.trans (Nat.le_succ _)) (Nat.le_succ (m+1))).year _ le_rfl (Nat.le_succ _))
  have horizonBound : horizon Q (m+1) (m+2) ≤ M*H := by
    simp only [horizon,clock,same,show m+2-(m+1)=1 by omega,Nat.cast_one]
    change zz L (m+1) + (L.S.scale (m+2)-L.S.scale (m+1)) + 1 ≤ _
    dsimp only [M]
    nlinarith [y₁.trans hβ, le_abs_self (L.S.scale (m+2)), neg_abs_le (L.S.scale (m+1))]
  have buy : T.buy (horizon Q (m+1) (m+2)) ≤ T.x*M^T.d*H^T.d := by
    calc _ ≤ T.x*(M*H)^T.d := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (zero_le_one.trans zpos) horizonBound T.d) hT
         _ = _ := by rw [mul_pow]; ring
  change T.buy (horizon Q (m+1) (m+2))^(m+2-(m+1))*b+b ≤ (T.x*M^T.d+1)*H^T.d*b
  rw [show m+2-(m+1)=1 by omega,pow_one]
  nlinarith [mul_le_mul_of_nonneg_right buy hb, mul_nonneg (sub_nonneg.mpr
    (one_le_pow₀ h1 : 1 ≤ H^T.d)) hb]

end YM.Integration.WilsonAdjacentWindingIncome
end

