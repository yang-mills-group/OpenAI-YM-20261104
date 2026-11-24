import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.LocalComparisonJetNormalization
import YM.FullVolume.Cross
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The original numerical schedule pays every fixed polynomial hull radius
against the original lattice denominator. One stage threshold works for
all physical periods and for both the coarse and fine hulls.
No ShortHulls or independent size assumption is used.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualNumericShortHulls
open Filter RG FullQLocal.RenderedStep
open scoped Topology

variable {G : Gauge} {V : Type} {C : Family G} {J : Request V}

/-- Both original cover radii are included in the same admitted cost. -/
theorem covers_le_cost (A : NumericSchedule C J) (m : ℕ) :
    1 + (C.path.levels.clock.coverSize m : ℝ) ≤ A.admittedCost m ∧
    1 + (C.path.levels.clock.coverSize (m + 1) : ℝ) ≤ A.admittedCost m := by
  let L := C.path.levels
  have hmon (k : ℕ) : 0 ≤ L.clock.monitor k := (Real.exp_pos _).le
  have hloop (k : ℕ) : 0 ≤ L.clock.loopCap k := by
    unfold Calendar.loopCap
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hmon k) _)
  have hc0 : 0 ≤ (L.clock.coverSize m : ℝ) := Nat.cast_nonneg _
  have hc1 : 0 ≤ (L.clock.coverSize (m + 1) : ℝ) := Nat.cast_nonneg _
  have h := A.cost_covers_geometry m
  change 1 + (L.clock.coverSize m : ℝ) + (L.clock.coverSize (m + 1) : ℝ) +
    L.clock.monitor m + L.clock.monitor (m + 1) +
    L.clock.loopCap m + L.clock.loopCap (m + 1) +
    (L.params m).paths + (L.params (m + 1)).paths +
    (L.params m).columns + (L.params (m + 1)).columns +
    (L.params m).clip.relaxation + (L.params (m + 1)).clip.relaxation ≤
      A.admittedCost m at h
  change 1 + (L.clock.coverSize m : ℝ) ≤ A.admittedCost m ∧
    1 + (L.clock.coverSize (m + 1) : ℝ) ≤ A.admittedCost m
  constructor <;> nlinarith [hmon m, hmon (m + 1), hloop m, hloop (m + 1),
    (L.params m).paths_pos, (L.params (m + 1)).paths_pos,
    (L.params m).columns_ge, (L.params (m + 1)).columns_ge,
    (L.params m).clip.radius_pos, (L.params (m + 1)).clip.radius_pos]

private theorem cost_le_hat (A : NumericSchedule C J) (hG : G.Simple)
    (hC : C.Makes) :
    ∀ᶠ m in atTop, A.admittedCost m ≤ 4 * C.path.levels.clock.hatBeta m := by
  obtain ⟨first, hfirst⟩ := A.cost_subpower 2 (by norm_num)
  filter_upwards [eventually_ge_atTop first,
    LocalComparison.JetNormalization.adjacent_beta C.path.levels hG] with m hm hnext
  have hcost := hfirst m hm (m + 1) 0 (Nat.lt_succ_self m)
  have hband := (hC.wilson.represents (m + 1) 0 (m + 1) le_rfl).band
  have hb : 0 < C.path.β (m + 1) 0 (m + 1) := by
    have hh := C.path.levels.fits.delayed (m + 1)
    linarith [hband.1]
  have he :
      Pert.Asymptotics.regulatorRun C (m + 1) 0 (m + 1) ^ (-(2 : ℝ)) =
        C.path.β (m + 1) 0 (m + 1) := by
    change IterationFour.Currency.gain (C.path.β (m + 1) 0 (m + 1)) ^
      (-(2 : ℝ)) = _
    rw [IterationFour.Currency.rpGain _ hb]
    norm_num
  rw [he] at hcost
  exact hcost.trans (hband.2.trans (by linarith))

private theorem hat_power_mesh_tendsto (L : Levels G) (n : ℕ) :
    Tendsto (fun m => L.clock.hatBeta m ^ n * L.S.a m) atTop (𝓝 0) := by
  let D := L.clock.bar + G.slopeConstant
  have hdecay : Tendsto (fun x : ℝ => x ^ n * Real.exp (-x)) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop n (b := (1 : ℝ))
      zero_lt_one).tendsto_div_nhds_zero
    exact h.congr (fun x => by rw [one_mul, div_eq_mul_inv, ← Real.exp_neg])
  have hbound := (hdecay.comp L.S.divergent).const_mul (D ^ n)
  rw [mul_zero] at hbound
  have hexp (m : ℕ) : Real.exp (-L.S.scale m) = L.S.a m := by
    unfold YM.Schedule.scale
    rw [Real.exp_neg, Real.exp_log (inv_pos.mpr (L.S.a_pos m)), inv_inv]
  apply squeeze_zero' (Eventually.of_forall fun m =>
    mul_nonneg (pow_nonneg (zero_lt_one.trans (L.fits.delayed m)).le n)
      (L.S.a_pos m).le) ?_ hbound
  filter_upwards [L.S.divergent.eventually_ge_atTop 1] with m hm
  have hbeta : L.clock.hatBeta m ≤ D * L.S.scale m := by
    have hbar := mul_le_mul_of_nonneg_left hm L.clock.bar_pos.le
    dsimp only [D]
    unfold Calendar.hatBeta
    nlinarith
  calc
    _ ≤ (D * L.S.scale m) ^ n * L.S.a m :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (zero_lt_one.trans (L.fits.delayed m)).le hbeta n)
        (L.S.a_pos m).le
    _ = D ^ n * (L.S.scale m ^ n * Real.exp (-L.S.scale m)) := by
      rw [mul_pow, hexp]
      ring

private theorem radius_le_hat (A : NumericSchedule C J) (K : NumericPrices A)
    (m k : ℕ) (hcost : A.admittedCost m ≤ 4 * C.path.levels.clock.hatBeta m)
    (hcover : 1 + (C.path.levels.clock.coverSize k : ℝ) ≤ A.admittedCost m) :
    (2 : ℝ) * ((K.hullMultiplier m : ℝ) *
      (1 + (C.path.levels.clock.coverSize k : ℝ))) ≤
      (8 * K.polynomialConstant * 8 ^ K.polynomialDegree) *
        C.path.levels.clock.hatBeta m ^ (K.polynomialDegree + 1) := by
  let b := C.path.levels.clock.hatBeta m
  have hb : 0 ≤ b := (zero_lt_one.trans (C.path.levels.fits.delayed m)).le
  have hc : 0 ≤ A.admittedCost m := A.admitted_cost_nonnegative m
  have h1 : 0 ≤ 1 + A.admittedCost m := by linarith
  have h8 : 1 + A.admittedCost m ≤ 8 * b := by
    have := A.admitted_cost_ge_one m
    change A.admittedCost m ≤ 4 * b at hcost
    linarith
  have hp : 0 ≤ K.polynomialConstant * (1 + A.admittedCost m) ^ K.polynomialDegree :=
    mul_nonneg K.polynomial_constant_nonnegative (pow_nonneg h1 _)
  have hp8 : 0 ≤ K.polynomialConstant * (8 * b) ^ K.polynomialDegree :=
    mul_nonneg K.polynomial_constant_nonnegative (pow_nonneg (by positivity) _)
  have hpoly :
      K.polynomialConstant * (1 + A.admittedCost m) ^ K.polynomialDegree ≤
        K.polynomialConstant * (8 * b) ^ K.polynomialDegree :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 h8 _)
      K.polynomial_constant_nonnegative
  calc
    _ ≤ 2 * (K.polynomialConstant * (1 + A.admittedCost m) ^ K.polynomialDegree *
        A.admittedCost m) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (K.hull_bound m) hcover (by positivity) hp) (by norm_num)
    _ ≤ 2 * (K.polynomialConstant * (8 * b) ^ K.polynomialDegree * (4 * b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hpoly hcost hc hp8) (by norm_num)
    _ = _ := by
      change _ = (8 * K.polynomialConstant * 8 ^ K.polynomialDegree) *
        b ^ (K.polynomialDegree + 1)
      rw [mul_pow, pow_succ]
      ring

private theorem denominator_le_side (S : YM.Schedule) (m p : ℕ) :
    ((S.denominator m).val : ℝ) ≤ ((S.side m p).val : ℝ) := by
  have hp : (1 : ℝ) ≤ ((S.period p).val : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (S.period p).property)
  change ((S.denominator m).val : ℝ) ≤
    (((S.period p).val * (S.denominator m).val : ℕ) : ℝ)
  rw [Nat.cast_mul]
  nlinarith [show (0 : ℝ) ≤ ((S.denominator m).val : ℝ) from Nat.cast_nonneg _]

/-- One event precedes every period, for both exact radii used by ShortHulls. -/
theorem eventually_sides (A : NumericSchedule C J) (K : NumericPrices A)
    (hG : G.Simple) (hC : C.Makes) :
    ∀ᶠ m in atTop, ∀ p : ℕ,
      2 * (K.hullMultiplier m * (1 + C.path.levels.clock.coverSize m)) <
        (C.side m p).val ∧
      2 * (K.hullMultiplier m * (1 + C.path.levels.clock.coverSize (m + 1))) <
        (C.side (m + 1) p).val := by
  let D := 8 * K.polynomialConstant * (8 : ℝ) ^ K.polynomialDegree
  have ht := (hat_power_mesh_tendsto C.path.levels (K.polynomialDegree + 1)).const_mul D
  rw [mul_zero] at ht
  filter_upwards [cost_le_hat A hG hC, ht.eventually_lt_const zero_lt_one] with m hm hsmall p
  have hden : D * C.path.levels.clock.hatBeta m ^ (K.polynomialDegree + 1) <
      ((C.S.denominator m).val : ℝ) := by
    have hsmall' :
        (D * C.path.levels.clock.hatBeta m ^ (K.polynomialDegree + 1)) * C.S.a m < 1 := by
      simpa only [mul_assoc] using hsmall
    have hh := (lt_div_iff₀ (C.S.a_pos m)).mpr hsmall'
    simpa only [one_div, YM.Schedule.a, inv_inv] using hh
  have hcoarse := radius_le_hat A K m m hm (covers_le_cost A m).1
  have hfine := radius_le_hat A K m (m + 1) hm (covers_le_cost A m).2
  have hdenNext : ((C.S.denominator m).val : ℝ) ≤
      ((C.S.denominator (m + 1)).val : ℝ) := by
    exact_mod_cast C.S.den_strict.monotone (Nat.le_succ m)
  constructor
  · exact_mod_cast hcoarse.trans_lt (hden.trans_le (denominator_le_side C.S m p))
  · exact_mod_cast hfine.trans_lt
      (hden.trans_le (hdenNext.trans (denominator_le_side C.S (m + 1) p)))

/-- Specialize without changing the Run, its schedule, or its selected price data. -/
theorem atRun (R : PhysicalNext.Repeat.Legato.Run G) (hG : G.Simple)
    {J : Request V} (A : NumericSchedule R.family J) (K : NumericPrices A) :
    ∀ᶠ m in atTop, ∀ p : ℕ,
      2 * (K.hullMultiplier m * (1 + R.family.path.levels.clock.coverSize m)) <
        (R.family.side m p).val ∧
      2 * (K.hullMultiplier m * (1 + R.family.path.levels.clock.coverSize (m + 1))) <
        (R.family.side (m + 1) p).val :=
  eventually_sides A K hG R.makes

end YM.Integration.ActualNumericShortHulls
end
