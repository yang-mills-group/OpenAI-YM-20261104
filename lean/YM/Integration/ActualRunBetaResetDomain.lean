import YM.Integration.ActualRunRatioGrowth
import YM.MatchingLedger.Compass.Deck

/-! The original Run enters the half-radius domain for its actual signed
adjacent-beta reset. The tail is chosen before every cutoff and period, and
the window consequence is uniform over all levels above its lower endpoint.
No Plan prediction or additional beta-difference estimate is assumed. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunBetaResetDomain
open Filter RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open MatchingLedger.Compass.Income
open scoped Topology

private theorem drift_le_log {G : Gauge} (A : Levels G) (m : ℕ) :
    (A.clock.params (m + 1)).drift ≤
      Real.log ((A.S.block m).val : ℝ) := by
  have hlarge := A.S.block_large m
  have hL : (1 : ℝ) < ((A.S.block m).val : ℝ) := by
    exact_mod_cast (show 1 < (A.S.block m).val from by omega)
  have hlog := Real.log_pos hL
  have hJnat := A.clock.adm (m + 1)
  have hJ : (1 : ℝ) ≤ (A.clock.J (m + 1) : ℝ) := by
    exact_mod_cast (show 1 ≤ A.clock.J (m + 1) from by omega)
  have hsq : (1 : ℝ) ≤ (A.clock.J (m + 1) : ℝ) ^ 2 := by nlinarith
  have hinv : ((A.clock.J (m + 1) : ℝ) ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hsq
  have hd := (A.fits.driftSmall m).trans hinv
  simpa only [one_mul] using (div_le_iff₀ hlog).mp hd

private theorem step_bound {G : Gauge} (R : Run G) (hG : G.Simple)
    (N p m : ℕ) (hm : m < N) :
    |R.family.path.β N p m - R.family.path.β N p (m + 1)| ≤
      (G.slopeConstant + 1) *
        Real.log ((R.alloy.B.a.S.block m).val : ℝ) := by
  let A := R.alloy.B.a
  let u := G.slopeConstant * Real.log ((A.S.block m).val : ℝ)
  have hlarge := A.S.block_large m
  have hL : (1 : ℝ) < ((A.S.block m).val : ℝ) := by
    exact_mod_cast (show 1 < (A.S.block m).val from by omega)
  have hu : 0 ≤ u := mul_nonneg (G.slopeConstant_pos hG).le
    (Real.log_pos hL).le
  have hs := (R.makes.wilson.steps N p m hm).2
  change |R.family.path.β N p (m + 1) - R.family.path.β N p m - u| ≤
    (A.clock.params (m + 1)).drift at hs
  calc
    |R.family.path.β N p m - R.family.path.β N p (m + 1)| =
        |R.family.path.β N p (m + 1) - R.family.path.β N p m| :=
      abs_sub_comm _ _
    _ = |(R.family.path.β N p (m + 1) - R.family.path.β N p m - u) + u| :=
      congrArg abs (sub_add_cancel _ u).symm
    _ ≤ |R.family.path.β N p (m + 1) - R.family.path.β N p m - u| + |u| :=
      abs_add_le _ _
    _ ≤ (A.clock.params (m + 1)).drift + u :=
      add_le_add hs (le_of_eq (abs_of_nonneg hu))
    _ ≤ Real.log ((A.S.block m).val : ℝ) + u :=
      add_le_add (drift_le_log A m) (le_refl u)
    _ = _ := by dsimp only [u, A]; ring

/-- The original same-Run transfer bound, before taking any level tail. -/
theorem adjacent_step_bound {G : Gauge} (R : Run G) (hG : G.Simple)
    (N p m : ℕ) (hm : m < N) :
    |R.family.path.β N p m - R.family.path.β N p (m + 1)| ≤
      (G.slopeConstant + 1) *
        Real.log ((R.alloy.B.a.S.block m).val : ℝ) :=
  step_bound R hG N p m hm

/-- The level tail is independent of the fine cutoff and physical period. -/
theorem half_radius {G : Gauge} (R : Run G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      |(R.family.path.β N p m - R.family.path.β N p (m + 1)) *
        regulatorRun R.family N p m ^ 2| ≤ (1 / 2 : ℝ) := by
  let A := R.alloy.B.a
  have hbound :=
    (Real.isLittleO_log_id_atTop.const_mul_left (G.slopeConstant + 1)).bound
      (show (0 : ℝ) < 1 / 8 by norm_num)
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
        (1 / 8 : ℝ) * |A.clock.hatBeta (m + 1)| := by
    simpa only [Real.norm_eq_abs, id_eq, Function.comp_apply] using hm
  rw [abs_of_pos hp] at hlogbound
  have hsmall : (G.slopeConstant + 1) *
      Real.log ((A.S.block m).val : ℝ) ≤ A.clock.hatBeta (m + 1) / 8 := by
    calc
      _ ≤ (G.slopeConstant + 1) * Real.log (A.clock.hatBeta (m + 1)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans hL) hLB)
          (by linarith [G.slopeConstant_pos hG])
      _ ≤ |(G.slopeConstant + 1) * Real.log (A.clock.hatBeta (m + 1))| :=
        le_abs_self _
      _ ≤ (1 / 8 : ℝ) * A.clock.hatBeta (m + 1) := hlogbound
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
    linarith
  have hdelta := step_bound R hG N p m hN
  have hhalf : |R.family.path.β N p m - R.family.path.β N p (m + 1)| ≤
      R.family.path.β N p m / 2 := by
    change |R.family.path.β N p m - R.family.path.β N p (m + 1)| ≤
      (G.slopeConstant + 1) * Real.log ((A.S.block m).val : ℝ) at hdelta
    linarith
  rw [abs_mul, abs_of_nonneg (sq_nonneg (regulatorRun R.family N p m))]
  calc
    _ ≤ (R.family.path.β N p m / 2) * regulatorRun R.family N p m ^ 2 :=
      mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
    _ = (R.family.path.β N p m * regulatorRun R.family N p m ^ 2) / 2 := by ring
    _ = 1 / 2 := by rw [Weather.epoch R.family R.makes hN.le p]

/-- Every level of a window is covered once its lower endpoint tends to
infinity. The same event still precedes all cutoffs and periods. -/
theorem window_half_radius {G : Gauge} (R : Run G) (hG : G.Simple)
    {ι : Type*} {l : Filter ι} (lower : ι → ℕ)
    (hlower : Tendsto lower l atTop) :
    ∀ᶠ a in l, ∀ m : ℕ, lower a ≤ m → ∀ N p : ℕ, m < N →
      |(R.family.path.β N p m - R.family.path.β N p (m + 1)) *
        regulatorRun R.family N p m ^ 2| ≤ (1 / 2 : ℝ) := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 (half_radius R hG)
  filter_upwards [hlower.eventually (eventually_ge_atTop M)] with a ha
  intro m hm N p hN
  exact hM m (ha.trans hm) N p hN

end YM.Integration.ActualRunBetaResetDomain
end
