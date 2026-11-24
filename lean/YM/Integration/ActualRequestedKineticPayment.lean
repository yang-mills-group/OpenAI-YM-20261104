import YM.Integration.NativeKineticCalibrationPrice
import YM.Integration.ActualCoinRequestedCalibration
import YM.Integration.ActualRunQLocalAdmission

/-! Fixed requested norms for the complete nonzero kinetic calibration.
The native FixedWave strengthens the scalar receipt of the same Coin; it
does not select another model or alter any field, activity, list or gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRequestedKineticPayment
open WilsonStartup
open PhysicalNext.Repeat.Legato
open Filter Lattice Wilson RG FullQLocal
open AnalyticBridge VerifiedReset Collection
open IterationFour IterationFour.Vacuum
open ActualRunAdmissionScales ActualRunAdmissionClock
open scoped Topology BigOperators

variable {G : Gauge}

/-- The coefficient and degree are fixed before the stage and its original
clip; only the requested norm orders and support exponent enter them. -/
theorem unitCost_monitor (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A)
    (ord pow : ℕ) (supp : ℝ) (hord : 6 ≤ ord) (hpow : 2 ≤ pow)
    (hsupp : 0 < supp) :
    ∃ K : ℝ, 0 < K ∧ ∃ E : ℕ, ∀ᶠ m in atTop, ∀ c : Clip, c.direct ≤ 1 →
      NativeKineticCalibration.unitCost G c
        (requestedBudget A m ord pow supp hord hpow hsupp)
        (A.params m).width (A.params m).paths ≤ K * A.clock.monitor m ^ E := by
  let p₀ := requestedBudget A 0 ord pow supp hord hpow hsupp
  let D := NativeKineticCalibrationPrice.degree p₀
  let K := 2 * NativeKineticCalibrationPrice.coefficient G p₀ * (5 : ℝ)^D
  have hcoef := NativeKineticCalibrationPrice.coefficient_positive G p₀
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, D+6, ?_⟩
  filter_upwards [cover_monitor A hG, rate_scale A hG 1 zero_lt_one,
    (Real.tendsto_log_atTop.comp (WardBin.bell A hG)).eventually_ge_atTop 1]
    with m hcover hr hz c hc
  let M := A.clock.monitor m
  have hM1 : 1 ≤ M := monitor_one A m
  have hM : 0 ≤ M := zero_le_one.trans hM1
  have hsq : (Real.log (A.clock.hatBeta m))^2 ≤ (A.clock.coverSize m : ℝ) :=
    Nat.le_ceil _
  have hlog : Real.log (A.clock.hatBeta m) ≤ M := by
    change 1 + (A.clock.coverSize m : ℝ) ≤ M at hcover
    nlinarith
  have henv : ActualRunAdmissionClock.envelope A m ≤ M := by
    simp only [one_mul] at hr
    linarith
  have hprofile := (profile_coarse A hG hMesh m).trans henv
  have hw := (profileCost_components A m).1.trans hprofile
  have hp := (profileCost_components A m).2.1.trans hprofile
  have hwidth := (A.params m).width_pos
  have hw5 : 1 + 4 * (A.params m).width⁻¹ ≤ 5*M := by linarith
  have hp2 : 1 + (A.params m).paths^2 ≤ 2*M^2 := by
    have hs := pow_le_pow_left₀ (A.params m).paths_pos.le hp 2
    have hm2 : 1 ≤ M^2 := one_le_pow₀ hM1
    linarith
  have hB : 1 + ((requestedBudget A m ord pow supp hord hpow hsupp).B : ℝ) ≤ M :=
    hcover
  have hbase := NativeKineticCalibrationPrice.unitCost_polynomial G
    (requestedBudget A m ord pow supp hord hpow hsupp) c
    (A.params m).width_pos (A.params m).paths_pos.le hc
  obtain ⟨hD, hC⟩ := NativeKineticCalibrationPrice.fields G
    (requestedBudget A m ord pow supp hord hpow hsupp) p₀ rfl rfl rfl
  rw [hD, hC] at hbase
  calc
    _ ≤ NativeKineticCalibrationPrice.coefficient G p₀ *
        (1 + 4 * (A.params m).width⁻¹)^D *
        (1 + (A.params m).paths^2) *
        (1 + ((requestedBudget A m ord pow supp hord hpow hsupp).B : ℝ))^4 :=
      hbase
    _ ≤ NativeKineticCalibrationPrice.coefficient G p₀ *
        (5*M)^D * (2*M^2) * M^4 := by
      apply mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) hB 4)
        (by positivity) (by positivity)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hw5 D) hcoef.le)
        hp2 (by positivity) (by positivity)
    _ = K * M^(D+6) := by
      dsimp only [K]
      rw [mul_pow, pow_add]
      ring

/-- Any fixed target currency is paid with one additional hat-coupling power;
the whole regular and full-hit price is retained. -/
theorem unitCost_weight (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A)
    (ord pow : ℕ) (supp : ℝ) (hord : 6 ≤ ord) (hpow : 2 ≤ pow)
    (hsupp : 0 < supp) (t κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ m in atTop, ∀ c : Clip, c.direct ≤ 1 →
      Currency.weight A (t+1) m *
        NativeKineticCalibration.unitCost G c
          (requestedBudget A m ord pow supp hord hpow hsupp)
          (A.params m).width (A.params m).paths ≤ κ * Currency.weight A t m := by
  obtain ⟨K, _hK, E, hcost⟩ :=
    unitCost_monitor A hG hMesh ord pow supp hord hpow hsupp
  have ht := (LocalComparison.JetNormalization.monitor_hat_tendsto A hG E 1
    zero_lt_one).const_mul K
  rw [mul_zero] at ht
  filter_upwards [hcost, ht.eventually_le_const hκ] with m hcost hm c hc
  calc
    _ ≤ Currency.weight A (t+1) m * (K * A.clock.monitor m^E) :=
      mul_le_mul_of_nonneg_left (hcost c hc) (Currency.weight_pos A m (t+1)).le
    _ = Currency.weight A t m *
        (K * (A.clock.monitor m^E * A.clock.hatCoupling m^(1 : ℝ))) := by
      rw [Currency.weight_add,
        show Currency.weight A 1 m = A.clock.hatCoupling m^(1 : ℝ) from rfl]
      ring
    _ ≤ Currency.weight A t m * κ :=
      mul_le_mul_of_nonneg_left hm (Currency.weight_pos A m t).le
    _ = κ * Currency.weight A t m := mul_comm _ _

/-- Every already-given native Coin on the same original Run has a flat
requested-norm kinetic calibration. FixedWave strengthens only its scalar
proof, uniformly before the cutoff, period, list and full remainder. -/
theorem atRun (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (ord pow : ℕ) (supp : ℝ) (hord : 6 ≤ ord) (hpow : 2 ≤ pow)
    (hsupp : 0 < supp) (t κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ m in atTop, ∀ N per : ℕ, m ≤ N →
      ∀ (S : List (Piece G (R.family.side m per))) (U : Rep G (R.family.side m per))
        (x γ l : ℝ), Coin R.family N per m S U x γ l →
      Decent (R.family.path.levels.params m).clip (R.family.path.levels.budget m) →
      Geo.Width
        (requestedBudget R.family.path.levels m ord pow supp hord hpow hsupp)
        (R.family.path.levels.params m).clip (R.family.path.levels.params m).width →
      NativeKineticCalibration.price G (R.family.path.levels.params m).clip
        (requestedBudget R.family.path.levels m ord pow supp hord hpow hsupp)
        (R.family.path.levels.params m).width (R.family.path.levels.params m).paths
        (U.beta - R.family.path.β N per m) ≤
          κ * Currency.weight R.family.path.levels t m := by
  let A := R.family.path.levels
  filter_upwards [unitCost_weight A hG
      (ActualRunQLocalAdmission.actual_preMesh R hReadout)
      ord pow supp hord hpow hsupp t κ hκ,
    IterationFour.Vacuum.waves (C := R.family) hG R.makes (t+1)]
    with m hcost hwave N per hi S U x γ l h hd hw
  have hδ : |U.beta - R.family.path.β N per m| ≤ Currency.weight A (t+1) m :=
    hwave N per hi (loaded R.family N per m S U)
      (h.lawful R.makes hi) h.types.budget h.value
  have h' : Coin R.family N per m S U x γ (Currency.weight A (t+1) m) :=
    ⟨h.types, h.error, h.total, h.lives, h.value, hδ⟩
  exact (ActualCoinRequestedCalibration.price_le ord pow supp hord hpow hsupp
    R.makes hi h' hw).trans (hcost (A.params m).clip hd.direct)

end YM.Integration.ActualRequestedKineticPayment
end
