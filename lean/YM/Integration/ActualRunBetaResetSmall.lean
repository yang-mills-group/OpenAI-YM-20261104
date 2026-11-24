import YM.Integration.ActualRunBetaResetDomain
import YM.Integration.ActualRunRetuningFirstOrder

/-!
The actual relative adjacent-beta increment tends to zero uniformly over
the fine cutoff and period. Consequently the complete scalar retuning bill
is eventually at most 1+epsilon at every bounded signed power and every
truncation order, including zero, on the same original Run.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunBetaResetSmall

open Filter RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open MatchingLedger.Compass.Income ActualBetaRemainder
open scoped Topology

theorem eventually_small {G : Gauge} (R : Run G) (hG : G.Simple)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      |(R.family.path.β N p m - R.family.path.β N p (m + 1)) *
        regulatorRun R.family N p m ^ 2| ≤ ε := by
  let A := R.alloy.B.a
  let η : ℝ := min (1 / 8) (ε / 4)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hη8 : η ≤ 1 / 8 := min_le_left _ _
  have hηε : η ≤ ε / 4 := min_le_right _ _
  have hbound :=
    (Real.isLittleO_log_id_atTop.const_mul_left (G.slopeConstant + 1)).bound hη
  have ht := (WardBin.bell A hG).comp (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually hbound] with m hm
  intro N p hN
  have hp := WardBin.hot A (m + 1)
  have hlarge := A.S.block_large m
  have hL : (1 : ℝ) < ((A.S.block m).val : ℝ) := by
    exact_mod_cast (show 1 < (A.S.block m).val from by omega)
  have hlog := (Real.log_pos hL).le
  have hLB : ((A.S.block m).val : ℝ) ≤ A.clock.hatBeta (m + 1) := by
    simpa only [Nat.zero_add, pow_one] using
      ActualRunRatioGrowth.ratio_power_le R hG m 0 (Nat.zero_le _)
  have hlogbound :
      |(G.slopeConstant + 1) * Real.log (A.clock.hatBeta (m + 1))| ≤
        η * |A.clock.hatBeta (m + 1)| := by
    simpa only [Real.norm_eq_abs, id_eq, Function.comp_apply] using hm
  rw [abs_of_pos hp] at hlogbound
  have hsmall : (G.slopeConstant + 1) *
      Real.log ((A.S.block m).val : ℝ) ≤ η * A.clock.hatBeta (m + 1) := by
    calc
      _ ≤ (G.slopeConstant + 1) * Real.log (A.clock.hatBeta (m + 1)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans hL) hLB)
          (by linarith [G.slopeConstant_pos hG])
      _ ≤ |(G.slopeConstant + 1) * Real.log (A.clock.hatBeta (m + 1))| :=
        le_abs_self _
      _ ≤ η * A.clock.hatBeta (m + 1) := hlogbound
  have hsmall8 : (G.slopeConstant + 1) *
      Real.log ((A.S.block m).val : ℝ) ≤ A.clock.hatBeta (m + 1) / 8 := by
    calc
      _ ≤ η * A.clock.hatBeta (m + 1) := hsmall
      _ ≤ (1 / 8 : ℝ) * A.clock.hatBeta (m + 1) :=
        mul_le_mul_of_nonneg_right hη8 hp.le
      _ = _ := by ring
  have he := Push.PriceCompiler.beta_eq R.alloy.B.valid m
  rw [← Push.PriceCompiler.block_eq R.alloy.B.valid m] at he
  change A.clock.hatBeta (m + 1) = A.clock.hatBeta m +
    G.slopeConstant * Real.log ((A.S.block m).val : ℝ) at he
  have hb := (R.makes.wilson.represents N p m hN.le).band.1
  change A.clock.hatBeta m / 2 ≤ R.family.path.β N p m at hb
  have hs : G.slopeConstant * Real.log ((A.S.block m).val : ℝ) ≤
      (G.slopeConstant + 1) * Real.log ((A.S.block m).val : ℝ) := by
    nlinarith
  have hdom : A.clock.hatBeta (m + 1) / 4 ≤ R.family.path.β N p m := by
    nlinarith
  have hdelta := ActualRunBetaResetDomain.adjacent_step_bound R hG N p m hN
  have hrelative : |R.family.path.β N p m - R.family.path.β N p (m + 1)| ≤
      ε * R.family.path.β N p m := by
    calc
      _ ≤ (G.slopeConstant + 1) * Real.log ((A.S.block m).val : ℝ) := hdelta
      _ ≤ η * A.clock.hatBeta (m + 1) := hsmall
      _ ≤ (ε / 4) * A.clock.hatBeta (m + 1) :=
        mul_le_mul_of_nonneg_right hηε hp.le
      _ = ε * (A.clock.hatBeta (m + 1) / 4) := by ring
      _ ≤ ε * R.family.path.β N p m := mul_le_mul_of_nonneg_left hdom hε.le
  rw [abs_mul, abs_of_nonneg (sq_nonneg (regulatorRun R.family N p m))]
  calc
    _ ≤ (ε * R.family.path.β N p m) * regulatorRun R.family N p m ^ 2 :=
      mul_le_mul_of_nonneg_right hrelative (sq_nonneg _)
    _ = ε * (R.family.path.β N p m * regulatorRun R.family N p m ^ 2) := by ring
    _ = ε := by rw [Weather.epoch R.family R.makes hN.le p, mul_one]

/-- The tail may depend on the order cap, but the per-step upper bound is
arbitrarily close to one and is uniform in every physical cutoff/period. -/
theorem retuning_bill_near_one (cap : ℕ) {G : Gauge} (R : Run G) (hG : G.Simple)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ n : ℕ,
        coefficientBill e
            (R.family.path.β N p m - R.family.path.β N p (m + 1))
            (regulatorRun R.family N p m) n +
          |correctionCoefficient e
            (R.family.path.β N p m - R.family.path.β N p (m + 1))
            (regulatorRun R.family N p m) n| *
            |regulatorRun R.family N p m| ^ (2 * n) ≤ 1 + ε := by
  obtain ⟨D, hD, hbound⟩ := ActualRunRetuningFirstOrder.uniform_cost cap
  filter_upwards [hbound R hG, eventually_small R hG (div_pos hε hD)] with m hm hs
  intro N p hN e he n
  refine (hm N p hN e he n).trans ?_
  have hmul := mul_le_mul_of_nonneg_left (hs N p hN) hD.le
  have hcancel : D * (ε / D) = ε := by
    calc
      _ = (ε / D) * D := mul_comm _ _
      _ = ε := div_mul_cancel₀ ε hD.ne'
  linarith

end YM.Integration.ActualRunBetaResetSmall
end
