import YM.Integration.WilsonMeasuredWindow
import YM.IterationFour.Running
import YM.Next.SCHEDULE.Clocks

/-!
Numerical prices for the original local field jets.  The expansion parameter
is the actual fine coupling, and every threshold precedes the cutoff and
period.  No derivative of a forced value envelope is inferred here.

The centered field chart A ↦ increment U (g • A) has relative direction
scale g / threshold.  The final theorem separately pays the exact physical
engineering ratio at the measured stop; it does not replace that stop by N.
-/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.LocalComparison.JetPrices

open Function Filter RG
open WilsonMeasuredAdmission (mast mast_pos mast_monotone)
open scoped Topology

variable {G : Gauge}

/-- The fine expansion parameter is bounded using the same physical history. -/
theorem fine_gain_le (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (m N period : ℕ) (hm : m < N) :
    Pert.Asymptotics.regulatorRun C N period (m + 1) ≤
      2 * C.path.levels.clock.hatCoupling m := by
  have hf := (IterationFour.Currency.hat_g hC N period (m + 1)
    (by omega : m + 1 ≤ N)).2
  have hmono : C.path.levels.clock.hatCoupling (m + 1) ≤
      C.path.levels.clock.hatCoupling m :=
    inv_anti₀ (Real.sqrt_pos.mpr (WardBin.hot C.path.levels m))
      (Real.sqrt_le_sqrt (Push.Corrected.Last.band_le C.path.levels hG
        (Nat.le_succ m)))
  exact hf.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))

/-- The original threshold cancels the coupling in a centered physical field
increment, leaving the actual monitor rather than an inverse coupling loss. -/
theorem fine_threshold_ratio (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (m N period : ℕ) (hm : m < N) :
    Pert.Asymptotics.regulatorRun C N period (m + 1) /
        (C.path.levels.budget m).threshold ≤
      2 / C.path.levels.clock.monitor m := by
  have h := fine_gain_le C hG hC m N period hm
  have hp : 0 < C.path.levels.clock.monitor m := Real.exp_pos _
  apply (div_le_div_iff₀ (C.path.levels.budget m).threshold_pos hp).mpr
  change Pert.Asymptotics.regulatorRun C N period (m + 1) *
      C.path.levels.clock.monitor m ≤
    2 * (C.path.levels.clock.hatCoupling m * C.path.levels.clock.monitor m)
  nlinarith only [mul_le_mul_of_nonneg_right h hp.le]

/-- One late-stage threshold controls every natural derivative power of the
centered chart scale; it does not provide derivative bounds for the function. -/
theorem fine_threshold_powers (C : Family G) (hG : G.Simple) (hC : C.Makes) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N → ∀ k : ℕ,
      (Pert.Asymptotics.regulatorRun C N period (m + 1) /
        (C.path.levels.budget m).threshold) ^ k ≤ 1 := by
  filter_upwards [(WardBin.mid C.path.levels hG).eventually_ge_atTop 2]
    with m hm N period hN k
  have hg := IterationFour.Currency.g_pos hC N period (m + 1)
    (by omega : m + 1 ≤ N)
  apply pow_le_one₀ (div_nonneg hg.le (C.path.levels.budget m).threshold_pos.le)
  exact (fine_threshold_ratio C hG hC m N period hN).trans
    ((div_le_one (Real.exp_pos _)).mpr hm)

/-- A fixed mast power is negligible in the original coupling scale. -/
theorem mast_hat_tendsto (A : Levels G) (hG : G.Simple)
    (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ => mast A m ^ q * A.clock.hatCoupling m ^ ε)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun m : ℕ =>
      WilsonAdmissionScale.logarithm A m ^ q * A.clock.hatCoupling m ^ ε)
      atTop (𝓝 0) := by
    refine ((Next.Scheduling.Clock.light 1 (q : ℝ) ε hε).comp
      (WardBin.bell A hG)).congr' (Eventually.of_forall fun m => ?_)
    simp only [comp_apply, Next.Scheduling.Clock.watch, Real.rpow_one,
      Next.Scheduling.Clock.tick, Real.exp_log (Real.log_pos (A.fits.delayed m)),
      Real.rpow_natCast, Next.Scheduling.Clock.gap, Calendar.hatCoupling,
      WilsonAdmissionScale.logarithm]
  have hupper := hlog.const_mul ((3 : ℝ) ^ q)
  rw [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun m =>
    mul_nonneg (pow_nonneg (mast_pos A m).le q)
      (Real.rpow_nonneg (WardBin.stepG A m).le ε)) ?_ hupper
  filter_upwards [(WilsonAdmissionScale.logarithm_tendsto A hG).eventually_ge_atTop 1]
    with m hm
  have hbase : mast A m ≤ 3 * WilsonAdmissionScale.logarithm A m := by
    dsimp only [mast]
    linarith
  have hpow := pow_le_pow_left₀ (mast_pos A m).le hbase q
  rw [mul_pow] at hpow
  exact (mul_le_mul_of_nonneg_right hpow
    (Real.rpow_nonneg (WardBin.stepG A m).le ε)).trans_eq (by ring)

/-- Fixed local powers and constants are paid uniformly by any prescribed
inverse power of the actual fine coupling, without changing that coupling. -/
theorem actual_mast_payment (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (q : ℕ) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      c * mast C.path.levels m ^ q ≤
        Pert.Asymptotics.regulatorRun C N period (m + 1) ^ (-ε) := by
  have ht := (mast_hat_tendsto C.path.levels hG q ε hε).const_mul
    (c * (2 : ℝ) ^ ε)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one] with m hm N period hN
  let g := Pert.Asymptotics.regulatorRun C N period (m + 1)
  have hg : 0 < g := IterationFour.Currency.g_pos hC N period (m + 1)
    (by omega : m + 1 ≤ N)
  have hgp : g ^ ε ≤ (2 : ℝ) ^ ε * C.path.levels.clock.hatCoupling m ^ ε := by
    calc
      g ^ ε ≤ (2 * C.path.levels.clock.hatCoupling m) ^ ε :=
        Real.rpow_le_rpow hg.le (fine_gain_le C hG hC m N period hN) hε.le
      _ = _ := Real.mul_rpow (by norm_num) (WardBin.stepG C.path.levels m).le
  have hpaid : (c * mast C.path.levels m ^ q) * g ^ ε ≤ 1 := by
    calc
      _ ≤ (c * mast C.path.levels m ^ q) *
          ((2 : ℝ) ^ ε * C.path.levels.clock.hatCoupling m ^ ε) :=
        mul_le_mul_of_nonneg_left hgp
          (mul_nonneg hc (pow_nonneg (mast_pos C.path.levels m).le q))
      _ = (c * (2 : ℝ) ^ ε) *
          (mast C.path.levels m ^ q * C.path.levels.clock.hatCoupling m ^ ε) := by ring
      _ ≤ 1 := hm
  change c * mast C.path.levels m ^ q ≤ g ^ (-ε)
  rw [Real.rpow_neg hg.le, ← one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hg ε)).mpr hpaid

/-- The measured stop pays the physical engineering ratio in coupling units.
The original physical radius r is retained, and the stop is selected from
rho. This does not assert an unweighted a_m^(-d) bound. -/
theorem window_engineering_payment (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (K d : ℕ) (hK : 0 < K)
    (paced : ∀ m, ((C.S.block m).val : ℝ) ≤
      WilsonAdmissionScale.logarithm C.path.levels m)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ rho : ℝ in 𝓝[>] 0, ∀ r : ℝ, 0 ≤ r → r ≤ rho →
      let m := WilsonMeasuredWindow.stop C.path.levels hG K rho
      ∀ N period : ℕ, m < N →
        c * (r / C.S.a m) ^ d ≤
          Pert.Asymptotics.regulatorRun C N period (m + 1) ^ (-ε) := by
  have ht := (WilsonMeasuredWindow.stop_tendsto C.path.levels hG K hK).eventually
    (actual_mast_payment C hG hC ((K + 1) * d) c ε hc hε)
  have hs : ∀ᶠ rho : ℝ in 𝓝[>] 0, rho < C.S.a 0 :=
    (eventually_lt_nhds (C.S.a_pos 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hs, ht] with rho hrho hs hp r hr hrr m N period hN
  have hw := (WilsonMeasuredWindow.window C.path.levels hG K paced hK hrho hs.le).2
  have hratio : r / C.S.a m ≤ mast C.path.levels m ^ (K + 1) := by
    apply (div_le_iff₀ (C.S.a_pos m)).mpr
    exact hrr.trans (hw.trans_eq (mul_comm _ _))
  calc
    c * (r / C.S.a m) ^ d ≤ c * (mast C.path.levels m ^ (K + 1)) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg hr (C.S.a_pos m).le) hratio d) hc
    _ = c * mast C.path.levels m ^ ((K + 1) * d) := by rw [pow_mul]
    _ ≤ _ := hp N period hN

end YM.Integration.LocalComparison.JetPrices
