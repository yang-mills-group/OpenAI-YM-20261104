import YM.Integration.FullQLocalRawInheritedRate
import YM.FullVolume.Cross
import YM.Next.WARD_BIN.Hats

/-! Either adjacent calendar inverse-monitor term absorbs any fixed positive
inverse power of the corresponding physical inverse temperature. This applies,
in particular, to the native RG01 quarter-power coefficient on its original Run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.NativeInheritedRate

open Filter Lattice RG FullQLocal FullQLocal.RawInherited FullQLocal.RenderedStep
open PhysicalNext.Repeat.Legato
open scoped Topology

variable {G : Gauge}

/-- The exponent here can be any fixed positive real. The inverse-monitor
factor in the requested raw rate is retained. -/
theorem power_le_monitor (L : Levels G) (hG : G.Simple) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, (L.clock.hatBeta m) ^ (-a) ≤ (L.clock.monitor m)⁻¹ ^ 2 := by
  have hsmall : ∀ᶠ m : ℕ in atTop,
      ‖(Real.log (Real.log (L.clock.hatBeta m))) ^ 2‖ ≤ (a / 2) * ‖Real.log (L.clock.hatBeta m)‖ :=
    (Real.tendsto_log_atTop.comp (WardBin.bell L hG)).eventually
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).bound (half_pos ha))
  filter_upwards [hsmall] with m hm
  let b := L.clock.hatBeta m
  let q := Real.log (Real.log b)
  have hb : 0 < b := WardBin.hot L m
  have hl : 0 ≤ Real.log b := (Real.log_pos (L.fits.delayed m)).le
  change ‖q ^ 2‖ ≤ a / 2 * ‖Real.log b‖ at hm
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q), abs_of_nonneg hl] at hm
  have he : Real.log b * (-a) ≤ 2 * (-(q ^ 2)) := by nlinarith
  calc
    _ = Real.exp (Real.log b * (-a)) := Real.rpow_def_of_pos hb _
    _ ≤ Real.exp (2 * (-(q ^ 2))) := Real.exp_le_exp.mpr he
    _ = (L.clock.monitor m)⁻¹ ^ 2 := by
      change Real.exp (2 * (-(q ^ 2))) = (Real.exp (q ^ 2))⁻¹ ^ 2
      rw [← Real.exp_neg, ← Real.exp_nat_mul]
      norm_num

theorem monitor_le_shape (L : Levels G) (m : ℕ) :
    (L.clock.monitor m)⁻¹ ^ 2 ≤ shape L.clock 0 m := by
  have hg : 0 ≤ L.clock.hatCoupling m := by unfold Calendar.hatCoupling; positivity
  have ht : 0 ≤ L.clock.threshold m :=
    mul_nonneg hg (Real.exp_pos _).le
  simp only [shape, pow_zero, one_mul]
  linarith

/-- The post-block inverse temperature in the native coefficient is exactly
the upper adjacent calendar temperature for this Run. -/
theorem native_power_le_shape (R : Run G) (hG : G.Simple) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop,
      (Pressure.betaF G (R.family.path.levels.clock.hatBeta m)
        (R.rolls.L (R.family.path.levels.clock.J (m + 1)))) ^ (-a) ≤
        shape R.family.path.levels.clock 0 (m + 1) := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually
    (power_le_monitor R.family.path.levels hG ha)] with m hm
  have hstep : R.family.path.levels.clock.hatBeta (m + 1) =
      Pressure.betaF G (R.family.path.levels.clock.hatBeta m)
        (R.rolls.L (R.family.path.levels.clock.J (m + 1))) :=
    Push.PriceCompiler.beta_eq R.alloy.B.valid m
  rw [← hstep]
  exact hm.trans (monitor_le_shape R.family.path.levels (m + 1))

/-- A single native tail controls any exponent above the declared lower
bound. The order may change along the Run. -/
theorem native_powers_le_shape (R : Run G) (hG : G.Simple) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℝ, a ≤ b →
      (Pressure.betaF G (R.family.path.levels.clock.hatBeta m)
        (R.rolls.L (R.family.path.levels.clock.J (m + 1)))) ^ (-b) ≤
        shape R.family.path.levels.clock 0 (m + 1) := by
  filter_upwards [native_power_le_shape R hG ha] with m hm
  intro b hb
  have hstep := Push.PriceCompiler.beta_eq R.alloy.B.valid m
  have htemp : 1 ≤ Pressure.betaF G (R.family.path.levels.clock.hatBeta m)
      (R.rolls.L (R.family.path.levels.clock.J (m + 1))) :=
    hstep ▸ (R.family.path.levels.fits.delayed (m + 1)).le
  exact (Real.rpow_le_rpow_of_exponent_le htemp (neg_le_neg hb)).trans hm

/-- The quarter-power portion of physical retention and the whole additive
spill rate in the native RG01 step share one late threshold at every order.
The pre-block contribution to retention remains separate. -/
theorem pruning_rates (R : Run G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop,
      let b := R.family.path.levels.clock.hatBeta (m + 1)
      let rate := shape R.family.path.levels.clock 0 (m + 1)
      b ^ (-(1 / 4) : ℝ) ≤ rate ∧
      ∀ r : ℕ, b ^ (-((r + 1 : ℕ) / (2 : ℝ)) - 1 / 64) ≤ rate := by
  filter_upwards [native_powers_le_shape R hG (by norm_num : (0 : ℝ) < 1 / 4)]
    with m hm
  have hstep : R.family.path.levels.clock.hatBeta (m + 1) =
      Pressure.betaF G (R.family.path.levels.clock.hatBeta m)
        (R.rolls.L (R.family.path.levels.clock.J (m + 1))) :=
    Push.PriceCompiler.beta_eq R.alloy.B.valid m
  dsimp only
  rw [hstep]
  refine ⟨hm _ le_rfl, ?_⟩
  intro r
  have hb : (1 / 4 : ℝ) ≤ ((r + 1 : ℕ) / (2 : ℝ)) + 1 / 64 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have he : -(((r + 1 : ℕ) / (2 : ℝ)) + 1 / 64) =
      -((r + 1 : ℕ) / (2 : ℝ)) - 1 / 64 := by ring
  rw [← he]
  exact hm _ hb

/-- If the chosen price's vanishing coordinate is bounded by a native
positive-power class, its quantitative raw receipt uses the same post-price
and that very price family. -/
theorem receipt_of_native_power {V : Type} (R : Run G) (hG : G.Simple)
    {J : Request V} {A : NumericSchedule R.family J} (K : NumericPrices A)
    (post : (ℕ → ℕ) → ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (h : ∀ᶠ m : ℕ in atTop,
      K.vanishing m ≤ |post (fun i => (R.family.path.levels.clock.factor i).val)
        (R.family.path.levels.clock.J (m + 1))| *
      (Pressure.betaF G (R.family.path.levels.clock.hatBeta m)
        (R.rolls.L (R.family.path.levels.clock.J (m + 1)))) ^ (-a)) :
    Receipt K 0 post := by
  refine ⟨eventually_atTop.mp ?_⟩
  filter_upwards [h, native_power_le_shape R hG ha] with m hm hpow
  have hn : 0 ≤ shape R.family.path.levels.clock 0 m :=
    (sq_nonneg _).trans (monitor_le_shape R.family.path.levels m)
  exact hm.trans (mul_le_mul_of_nonneg_left
    (hpow.trans (le_add_of_nonneg_left hn)) (abs_nonneg _))

end YM.Integration.WilsonLimitConstruction.NativeInheritedRate
end
