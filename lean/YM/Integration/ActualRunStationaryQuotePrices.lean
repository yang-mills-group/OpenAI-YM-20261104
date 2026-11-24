import YM.Integration.RunStationaryQuotePurchase
import YM.Integration.LocalComparisonJetPrices

/-! The actual purchased stationary table bill costs an arbitrarily small
fixed inverse power of the original fine coupling. The stage threshold
precedes cutoff, period and every eligible requested table order. This pays
gross local prices; it is not a normalized calibration-column estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunStationaryQuotePrices

open Filter RG
open PhysicalNext.Repeat.Legato
open scoped Topology

variable {G : Gauge}

/-- The inverse-stage exponent is small before any cutoff or period is chosen. -/
theorem stage_cap_tendsto (A : Levels G) (hG : G.Simple)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ =>
      (A.clock.hatBeta m ^ ((1 : ℝ) / ((A.clock.J (m + 1) : ℝ) + 1))) ^ k *
        A.clock.hatCoupling m ^ ε) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_nat_gt ((4 * (k : ℝ)) / ε)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (A.fits.deep.eventually_ge_atTop K)
  have ht := (tendsto_rpow_neg_atTop (show 0 < ε / 4 by positivity)).comp
    (WardBin.bell A hG)
  apply squeeze_zero' (Eventually.of_forall fun m =>
    mul_nonneg (pow_nonneg (Real.rpow_nonneg (WardBin.hot A m).le _) k)
      (Real.rpow_nonneg (WardBin.stepG A m).le ε)) ?_ ht
  filter_upwards [eventually_ge_atTop M, (WardBin.bell A hG).eventually_ge_atTop 1]
    with m hm hβ
  have hJ : (K : ℝ) ≤ A.clock.J (m + 1) := by
    exact_mod_cast hM (m + 1) (hm.trans (Nat.le_succ m))
  have hk : 4 * (k : ℝ) < ε * K := by
    simpa only [mul_comm ε] using (div_lt_iff₀ hε).mp hK
  have he : (k : ℝ) / ((A.clock.J (m + 1) : ℝ) + 1) ≤ ε / 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hJ hε.le]
  have hp := WardBin.hot A m
  have hid :
      (A.clock.hatBeta m ^ ((1 : ℝ) / ((A.clock.J (m + 1) : ℝ) + 1))) ^ k *
        A.clock.hatCoupling m ^ ε =
      A.clock.hatBeta m ^
        ((k : ℝ) / ((A.clock.J (m + 1) : ℝ) + 1) - ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    unfold Calendar.hatCoupling
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hp.le, ← Real.rpow_mul hp.le,
      ← Real.rpow_add hp]
    congr 1
    ring
  rw [hid]
  exact Real.rpow_le_rpow_of_exponent_le hβ (by linarith)

/-- Every fixed power of the literal purchased bill is paid on the same Run.
All orders n allowed by the current stage share one threshold. -/
theorem actual_payment (R : Run G) (hG : G.Simple)
    (h : PhysicalNext.Repeat.Mallow.RG12.Earned
      (CommonStationaryQuotePurchase.request G) R.kit.shape R.alloy.delay)
    (k : ℕ) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N → ∀ n : ℕ,
      n ≤ R.alloy.B.a.clock.J (m + 1) →
      c * (CommonStationaryQuotes.bill
        ((ActualSpringStationaryService.quotes R m n).tables
          (R.alloy.B.a.params (m + 1)).clip
          (R.alloy.B.a.clock.op m period).patch)) ^ k ≤
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ (-ε) := by
  have ht := (stage_cap_tendsto R.alloy.B.a hG k ε hε).const_mul
    (c * (2 : ℝ) ^ ε)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one]
    with m hm N period hN n hn
  let B := CommonStationaryQuotes.bill
    ((ActualSpringStationaryService.quotes R m n).tables
      (R.alloy.B.a.params (m + 1)).clip (R.alloy.B.a.clock.op m period).patch)
  let g := Pert.Asymptotics.regulatorRun R.family N period (m + 1)
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N period (m + 1) (by omega)
  have hB : 0 ≤ B := by
    apply le_trans zero_le_one
    exact CommonStationaryQuotes.bill_ge_one G
      (R.alloy.B.a.params (m + 1)).width (R.alloy.B.a.params (m + 1)).paths
      (R.alloy.B.a.clock.J (m + 1)) R.alloy.B.a.clock.kernel n
      (R.alloy.B.a.params (m + 1)).width_pos
      (R.alloy.B.a.params (m + 1)).clip (R.alloy.B.a.clock.op m period).patch rfl
  have hcap := pow_le_pow_left₀ hB
    (RunStationaryQuotePurchase.actual_bound R h m n period hn) k
  have hgp : g ^ ε ≤ (2 : ℝ) ^ ε * R.alloy.B.a.clock.hatCoupling m ^ ε := by
    calc
      _ ≤ (2 * R.alloy.B.a.clock.hatCoupling m) ^ ε :=
        Real.rpow_le_rpow hg.le
          (LocalComparison.JetPrices.fine_gain_le R.family hG R.makes m N period hN) hε.le
      _ = _ := Real.mul_rpow (by norm_num) (WardBin.stepG R.alloy.B.a m).le
  have hpaid : (c * B ^ k) * g ^ ε ≤ 1 := by
    calc
      _ ≤ (c * (R.alloy.B.a.clock.hatBeta m ^
          ((1 : ℝ) / ((R.alloy.B.a.clock.J (m + 1) : ℝ) + 1))) ^ k) *
          ((2 : ℝ) ^ ε * R.alloy.B.a.clock.hatCoupling m ^ ε) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcap hc) hgp
          (Real.rpow_nonneg hg.le ε)
          (mul_nonneg hc (pow_nonneg
            (Real.rpow_nonneg (WardBin.hot R.alloy.B.a m).le _) k))
      _ = (c * (2 : ℝ) ^ ε) *
          ((R.alloy.B.a.clock.hatBeta m ^
            ((1 : ℝ) / ((R.alloy.B.a.clock.J (m + 1) : ℝ) + 1))) ^ k *
              R.alloy.B.a.clock.hatCoupling m ^ ε) := by ring
      _ ≤ 1 := hm
  change c * B ^ k ≤ g ^ (-ε)
  rw [Real.rpow_neg hg.le, ← one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hg ε)).mpr hpaid

end YM.Integration.ActualRunStationaryQuotePrices
