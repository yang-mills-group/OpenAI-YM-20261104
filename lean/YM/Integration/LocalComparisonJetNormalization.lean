import YM.Integration.LocalComparisonJetPrices

/-!
# The actual coarse threshold inside a larger fine-coupling chart

The adjacent hatted inverse couplings are compared using the original gentle
schedule.  The next-level physical band is then compared with that same coarse
clock.  A fixed local mast factor times the coarse threshold fits inside every
radius g_fine^s with s < 1, eventually before all cutoffs and periods.

The resulting bound controls every natural derivative power at once.  The mast
power and prefactor are fixed before the stage threshold; no assertion about a
growing stage-dependent power is made.
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.LocalComparison.JetNormalization

open Function Filter RG
open WilsonMeasuredAdmission (mast mast_pos)
open scoped Topology

variable {G : Gauge}

/-- This is the adjacent-clock argument already used in the native
`Push.Corrected.Grows.walls` proof, exposed without its cover conclusion. -/
theorem adjacent_beta (A : Levels G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, A.clock.hatBeta (m + 1) ≤ 2 * A.clock.hatBeta m := by
  filter_upwards [A.fits.mesh.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    A.S.divergent.eventually_gt_atTop 0] with m hm hscale
  have hlog : Real.log (A.S.block m).val ≤ A.S.scale m := by
    have hh : Real.log (A.S.block m).val / A.S.scale m ≤ 1 := hm
    simpa only [one_mul] using (div_le_iff₀ hscale).mp hh
  have hs := Gauge.slopeConstant_pos hG
  unfold Calendar.hatBeta
  rw [Schedule.scale_succ]
  nlinarith only [A.clock.bar_pos, mul_le_mul_of_nonneg_left hlog hs.le]

/-- The original coarse hatted coupling is controlled by the actual fine
coupling uniformly over every represented cutoff and period. -/
theorem coarse_hat_le_fine (C : Family G) (hG : G.Simple) (hC : C.Makes) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      C.path.levels.clock.hatCoupling m ≤
        2 * Pert.Asymptotics.regulatorRun C N period (m + 1) := by
  filter_upwards [adjacent_beta C.path.levels hG] with m hm N period hN
  have hb := (hC.wilson.represents N period (m + 1) (by omega)).band
  have hmono := Push.Corrected.Last.band_le C.path.levels hG (Nat.le_succ m)
  have hp := WardBin.hot C.path.levels m
  have hstripe : C.path.β N period (m + 1) ∈
      IterationFour.Currency.stripe (C.path.levels.clock.hatBeta m) := by
    constructor <;> nlinarith only [hb.1, hb.2, hm, hmono, hp]
  exact (IterationFour.Currency.sizes_band hp hstripe).1

/-- The reciprocal normalization factor is bounded in the correct direction;
the monitor is retained, rather than replaced by a constant. -/
theorem threshold_over_fine (C : Family G) (hG : G.Simple) (hC : C.Makes) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      (C.path.levels.budget m).threshold /
        Pert.Asymptotics.regulatorRun C N period (m + 1) ≤
          2 * C.path.levels.clock.monitor m := by
  filter_upwards [coarse_hat_le_fine C hG hC] with m hm N period hN
  have hg := IterationFour.Currency.g_pos hC N period (m + 1) (by omega)
  apply (div_le_iff₀ hg).mpr
  change C.path.levels.clock.hatCoupling m * C.path.levels.clock.monitor m ≤
    2 * C.path.levels.clock.monitor m * Pert.Asymptotics.regulatorRun C N period (m + 1)
  exact (mul_le_mul_of_nonneg_right (hm N period hN)
    (show 0 ≤ C.path.levels.clock.monitor m from (Real.exp_pos _).le)).trans_eq (by ring)

/-- Every fixed monitor power is negligible in the hatted coupling scale. -/
theorem monitor_hat_tendsto (A : Levels G) (hG : G.Simple)
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ => A.clock.monitor m ^ d * A.clock.hatCoupling m ^ ε)
      atTop (𝓝 0) := by
  refine ((Next.Scheduling.Clock.light 2 (d : ℝ) ε hε).comp
    (WardBin.bell A hG)).congr' (Eventually.of_forall fun m => ?_)
  simp only [comp_apply, Next.Scheduling.Clock.watch_two,
    Real.rpow_natCast, Calendar.monitor, Next.Scheduling.Clock.tick,
    Calendar.hatCoupling, Next.Scheduling.Clock.gap]

theorem mast_monitor_hat_tendsto (A : Levels G) (hG : G.Simple)
    (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ => mast A m ^ q * A.clock.monitor m *
      A.clock.hatCoupling m ^ ε) atTop (𝓝 0) := by
  have ht := (JetPrices.mast_hat_tendsto A hG q (ε / 2) (half_pos hε)).mul
    (monitor_hat_tendsto A hG 1 (ε / 2) (half_pos hε))
  simp only [pow_one, mul_zero] at ht
  refine ht.congr' (Eventually.of_forall fun m => ?_)
  calc
    (mast A m ^ q * A.clock.hatCoupling m ^ (ε / 2)) *
        (A.clock.monitor m * A.clock.hatCoupling m ^ (ε / 2)) =
      mast A m ^ q * A.clock.monitor m *
        (A.clock.hatCoupling m ^ (ε / 2) * A.clock.hatCoupling m ^ (ε / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add (WardBin.stepG A m), add_halves]

/-- A fixed local spatial price also fits inside the larger chart.  One stage
threshold works for all derivative powers, cutoffs and periods. -/
theorem weighted_threshold_radius_powers (C : Family G) (hG : G.Simple)
    (hC : C.Makes) (q : ℕ) (c s : ℝ) (hc : 0 ≤ c) (hs : s < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N → ∀ k : ℕ,
      (c * mast C.path.levels m ^ q * (C.path.levels.budget m).threshold /
        Pert.Asymptotics.regulatorRun C N period (m + 1) ^ s) ^ k ≤ 1 := by
  have he : 0 < 1 - s := sub_pos.mpr hs
  have ht := (mast_monitor_hat_tendsto C.path.levels hG q (1 - s) he).const_mul
    (2 * c * (2 : ℝ) ^ (1 - s))
  rw [mul_zero] at ht
  filter_upwards [coarse_hat_le_fine C hG hC, ht.eventually_le_const zero_lt_one]
    with m hm hpaid N period hN k
  let g := Pert.Asymptotics.regulatorRun C N period (m + 1)
  have hg : 0 < g := IterationFour.Currency.g_pos hC N period (m + 1) (by omega)
  have hmon : 0 ≤ C.path.levels.clock.monitor m := (Real.exp_pos _).le
  have hweight : 0 ≤ mast C.path.levels m ^ q * C.path.levels.clock.monitor m :=
    mul_nonneg (pow_nonneg (mast_pos C.path.levels m).le _) hmon
  have hnum : c * mast C.path.levels m ^ q * (C.path.levels.budget m).threshold ≤
      (2 * c) * (mast C.path.levels m ^ q * C.path.levels.clock.monitor m) * g := by
    change c * mast C.path.levels m ^ q *
      (C.path.levels.clock.hatCoupling m * C.path.levels.clock.monitor m) ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left (hm N period hN)
      (mul_nonneg hc hweight)]
  have hgp : g ^ (1 - s) ≤ (2 : ℝ) ^ (1 - s) *
      C.path.levels.clock.hatCoupling m ^ (1 - s) := by
    calc
      g ^ (1 - s) ≤ (2 * C.path.levels.clock.hatCoupling m) ^ (1 - s) :=
        Real.rpow_le_rpow hg.le (JetPrices.fine_gain_le C hG hC m N period hN) he.le
      _ = _ := Real.mul_rpow (by norm_num) (WardBin.stepG C.path.levels m).le
  have hratio : c * mast C.path.levels m ^ q * (C.path.levels.budget m).threshold /
      g ^ s ≤ 1 := by
    calc
      _ ≤ ((2 * c) * (mast C.path.levels m ^ q *
          C.path.levels.clock.monitor m) * g) / g ^ s :=
        div_le_div_of_nonneg_right hnum (Real.rpow_pos_of_pos hg s).le
      _ = (2 * c) * (mast C.path.levels m ^ q *
          C.path.levels.clock.monitor m) * g ^ (1 - s) := by
        rw [Real.rpow_sub hg, Real.rpow_one]
        ring
      _ ≤ (2 * c) * (mast C.path.levels m ^ q * C.path.levels.clock.monitor m) *
          ((2 : ℝ) ^ (1 - s) * C.path.levels.clock.hatCoupling m ^ (1 - s)) :=
        mul_le_mul_of_nonneg_left hgp (mul_nonneg (mul_nonneg (by norm_num) hc) hweight)
      _ = (2 * c * (2 : ℝ) ^ (1 - s)) *
          (mast C.path.levels m ^ q * C.path.levels.clock.monitor m *
            C.path.levels.clock.hatCoupling m ^ (1 - s)) := by ring
      _ ≤ 1 := hpaid
  apply pow_le_one₀ ?_ hratio
  exact div_nonneg (mul_nonneg (mul_nonneg hc (pow_nonneg (mast_pos C.path.levels m).le _))
    (C.path.levels.budget m).threshold_pos.le) (Real.rpow_pos_of_pos hg s).le

/-- The unweighted native threshold fits inside every g_fine^s chart, s < 1,
uniformly through all natural derivative orders. -/
theorem threshold_radius_powers (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (s : ℝ) (hs : s < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N → ∀ k : ℕ,
      ((C.path.levels.budget m).threshold /
        Pert.Asymptotics.regulatorRun C N period (m + 1) ^ s) ^ k ≤ 1 := by
  simpa only [pow_zero, one_mul] using
    weighted_threshold_radius_powers C hG hC 0 1 s zero_le_one hs

end YM.Integration.LocalComparison.JetNormalization
