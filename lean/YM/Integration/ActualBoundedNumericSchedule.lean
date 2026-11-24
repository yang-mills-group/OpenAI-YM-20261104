import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.ActualRunAdmissionClock

/-! A bounded input strip chosen before any analytic input or output.
All 27 numerical duties remain proved on the original Run.  The original
norms, output width, radii and calibration cap are retained.  Clipping the
path rate is paid by the actual cover/monitor tails, not by monotonicity
of the old faster exponential. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualBoundedNumericSchedule
open Filter Function Lattice Wilson RG
open PhysicalNext.Repeat.Legato FullQLocal.RenderedStep
open scoped Topology

variable {G : Gauge} {V : Type}

/-- A geometry term already gives room for the bounded-width cost. -/
private theorem two_le_cost {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (m : ℕ) : 2 ≤ A.admittedCost m := by
  let D := C.path.levels
  have hmonitor : 1 ≤ D.clock.monitor m := Real.one_le_exp (sq_nonneg _)
  have hmonitor' : 0 ≤ D.clock.monitor (m + 1) := Real.exp_nonneg _
  have hloop (k : ℕ) : 0 ≤ D.clock.loopCap k :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  have hcover0 : 0 ≤ (D.clock.coverSize m : ℝ) := Nat.cast_nonneg _
  have hcover1 : 0 ≤ (D.clock.coverSize (m + 1) : ℝ) := Nat.cast_nonneg _
  have hpath0 := (D.params m).paths_pos
  have hpath1 := (D.params (m + 1)).paths_pos
  have hcolumn0 := (D.params m).columns_ge
  have hcolumn1 := (D.params (m + 1)).columns_ge
  have hrelax0 := (D.params m).clip.radius_pos
  have hrelax1 := (D.params (m + 1)).clip.radius_pos
  have hbill := A.cost_covers_geometry m
  change 1 + (D.clock.coverSize m : ℝ) + (D.clock.coverSize (m + 1) : ℝ) +
    D.clock.monitor m + D.clock.monitor (m + 1) +
    D.clock.loopCap m + D.clock.loopCap (m + 1) +
    (D.params m).paths + (D.params (m + 1)).paths +
    (D.params m).columns + (D.params (m + 1)).columns +
    (D.params m).clip.relaxation + (D.params (m + 1)).clip.relaxation ≤
      A.admittedCost m at hbill
  linarith [hloop m, hloop (m + 1)]

private def cost {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (m : ℕ) : ℝ := 2 * A.admittedCost m

private theorem cost_nonnegative {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (m : ℕ) : 0 ≤ cost A m :=
  mul_nonneg (by norm_num) (A.admitted_cost_nonnegative m)

private theorem le_cost {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (m : ℕ) : A.admittedCost m ≤ cost A m := by
  have h := A.admitted_cost_nonnegative m
  unfold cost
  linarith

private theorem cost_le_square {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (m : ℕ) : cost A m ≤ A.admittedCost m ^ 2 := by
  simpa only [cost, pow_two] using
    mul_le_mul_of_nonneg_right (two_le_cost A m) (A.admitted_cost_nonnegative m)

private theorem cost_power {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (m a : ℕ) :
    cost A m ^ a ≤ A.admittedCost m ^ (2 * a) := by
  calc
    _ ≤ (A.admittedCost m ^ 2) ^ a :=
      pow_le_pow_left₀ (cost_nonnegative A m) (cost_le_square A m) a
    _ = _ := (pow_mul _ _ _).symm

private theorem inverse_min_one {x : ℝ} (hx : 0 < x) :
    (min x 1)⁻¹ ≤ x⁻¹ + 1 := by
  rcases le_total x 1 with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h, inv_one]
    exact le_add_of_nonneg_left (inv_nonneg.mpr hx.le)

/-- Doubling the bill preserves every subpower, using the old half exponent. -/
private theorem cost_subpower (R : Run G) {J : Request V}
    (A : NumericSchedule R.family J) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      cost A m ≤
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ (-epsilon) := by
  obtain ⟨start, hstart⟩ := A.cost_subpower (epsilon / 2) (half_pos hepsilon)
  filter_upwards [eventually_ge_atTop start] with m hm N period hN
  let g := Pert.Asymptotics.regulatorRun R.family N period (m + 1)
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N period (m + 1)
    (Nat.succ_le_of_lt hN)
  have hc : A.admittedCost m ≤ g ^ (-(epsilon / 2)) :=
    hstart m hm N period hN
  calc
    cost A m ≤ A.admittedCost m ^ 2 := cost_le_square A m
    _ ≤ (g ^ (-(epsilon / 2))) ^ 2 :=
      pow_le_pow_left₀ (A.admitted_cost_nonnegative m) hc 2
    _ = g ^ (-epsilon) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le]
      congr 1
      ring

/-- The old unit bill and its half-power bound control the actual fine
coupling from below.  No new pre-mesh or beta comparison premise is used. -/
private theorem actual_inverse_lower (R : Run G) {J : Request V}
    (A : NumericSchedule R.family J) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      (R.family.path.levels.clock.hatBeta m)⁻¹ ≤
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) := by
  obtain ⟨start, hstart⟩ := A.cost_subpower (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop start] with m hm N period hN
  let D := R.family.path.levels
  let g := Pert.Asymptotics.regulatorRun R.family N period (m + 1)
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N period (m + 1)
    (Nat.succ_le_of_lt hN)
  have hs : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hsquare : (Real.sqrt g) ^ 2 = g := Real.sq_sqrt hg.le
  have hc : A.admittedCost m ≤ (Real.sqrt g)⁻¹ := by
    have h := hstart m hm N period hN
    change A.admittedCost m ≤ g ^ (-(1 / 2 : ℝ)) at h
    rw [Real.rpow_neg hg.le, ← Real.sqrt_eq_rpow] at h
    exact h
  have hother : 0 ≤ D.clock.threshold (m + 1) / g :=
    div_nonneg (D.budget (m + 1)).threshold_pos.le hg.le
  have hunit := A.cost_covers_units m N period hN
  change D.clock.threshold m / g + D.clock.threshold (m + 1) / g ≤
    A.admittedCost m at hunit
  have hdiv : D.clock.threshold m / g ≤ A.admittedCost m := by linarith
  have htheta : D.clock.threshold m ≤ Real.sqrt g := by
    calc
      _ ≤ A.admittedCost m * g := (div_le_iff₀ hg).mp hdiv
      _ ≤ (Real.sqrt g)⁻¹ * g := mul_le_mul_of_nonneg_right hc hg.le
      _ = (Real.sqrt g)⁻¹ * (Real.sqrt g * Real.sqrt g) :=
        congrArg ((Real.sqrt g)⁻¹ * ·) (by simpa only [pow_two] using hsquare.symm)
      _ = Real.sqrt g := inv_mul_cancel_left₀ hs.ne' _
  have hmonitor : 1 ≤ D.clock.monitor m := Real.one_le_exp (sq_nonneg _)
  have hhat : D.clock.hatCoupling m ≤ Real.sqrt g :=
    (show D.clock.hatCoupling m ≤ D.clock.threshold m from
      le_mul_of_one_le_right (WardBin.stepG D m).le hmonitor).trans htheta
  have hsq := pow_le_pow_left₀ (WardBin.stepG D m).le hhat 2
  have hb : D.clock.hatCoupling m ^ 2 = (D.clock.hatBeta m)⁻¹ := by
    unfold Calendar.hatCoupling
    rw [inv_pow, Real.sq_sqrt (WardBin.hot D m).le]
  rw [hb, hsquare] at hsq
  exact hsq

private theorem regular_exponent (R : Run G) (hG : G.Simple) (D : ℝ) :
    ∀ᶠ m : ℕ in atTop, D * Real.log (R.family.path.levels.clock.hatBeta m) ≤
      (R.family.path.levels.clock.coverSize m : ℝ) := by
  let L := R.family.path.levels
  filter_upwards [(Real.tendsto_log_atTop.comp (WardBin.bell L hG)).eventually_ge_atTop D]
    with m hm
  have hz := (Real.log_pos (L.fits.delayed m)).le
  exact (show D * Real.log (L.clock.hatBeta m) ≤
    Real.log (L.clock.hatBeta m) ^ 2 by
      simpa only [Function.comp_apply, pow_two] using mul_le_mul_of_nonneg_right hm hz).trans (Nat.le_ceil _)

private theorem forced_exponent (R : Run G) (hG : G.Simple)
    (delta D : ℝ) (hdelta : 0 < delta) (hD : 0 ≤ D) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, D * Real.log (R.family.path.levels.clock.hatBeta m) ≤
      R.family.path.levels.clock.monitor m ^ delta /
        (1 + (R.family.path.levels.clock.coverSize m : ℝ)) ^ d := by
  let L := R.family.path.levels
  have ht := ((Next.Scheduling.Clock.ceiling_cheaper 2 delta (d + 1)
    (by norm_num) hdelta).comp (WardBin.bell L hG)).const_mul D
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one] with m hm
  let v : ℝ := 1 + (L.clock.coverSize m : ℝ)
  have hv : 0 < v := by dsimp [v]; positivity
  have hM : 0 < L.clock.monitor m ^ delta :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hpaid : D * v ^ (d + 1) ≤ L.clock.monitor m ^ delta := by
    have hq : D * (v ^ (d + 1) / L.clock.monitor m ^ delta) ≤ 1 := by
      simpa only [Function.comp_apply, Next.Scheduling.Clock.watch_two,
        Next.Scheduling.Clock.cover, Next.Scheduling.Clock.tick,
        Calendar.coverSize, Calendar.monitor, v] using hm
    have hdiv : D * v ^ (d + 1) / L.clock.monitor m ^ delta ≤ 1 := by
      simpa only [mul_div_assoc] using hq
    simpa only [one_mul] using (div_le_iff₀ hM).mp hdiv
  have hceil : Real.log (L.clock.hatBeta m) ^ 2 ≤ (L.clock.coverSize m : ℝ) :=
    Nat.le_ceil _
  have hzv : Real.log (L.clock.hatBeta m) ≤ v := by
    dsimp [v]
    nlinarith [sq_nonneg (Real.log (L.clock.hatBeta m) - (1 / 2 : ℝ))]
  have hproduct : D * Real.log (L.clock.hatBeta m) * v ^ d ≤ D * v ^ (d + 1) := by
    calc
      _ ≤ D * v * v ^ d := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hzv hD) (pow_nonneg hv.le _)
      _ = _ := by rw [pow_succ]; ring
  exact (le_div_iff₀ (pow_pos hv _)).mpr (hproduct.trans hpaid)

private theorem regular_one (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (a c t : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      cost A m ^ a *
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ (-(c : ℝ)) *
        Real.exp (-(R.family.path.levels.clock.coverSize m : ℝ)) ≤
      Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ t := by
  filter_upwards [cost_subpower R A 1 zero_lt_one, actual_inverse_lower R A,
    regular_exponent R hG ((a + c + t : ℕ) : ℝ)] with m hc hi he N period hN
  have hg := IterationFour.Currency.g_pos R.makes N period (m + 1)
    (Nat.succ_le_of_lt hN)
  have hcost : cost A m ≤
      (Pert.Asymptotics.regulatorRun R.family N period (m + 1))⁻¹ := by
    simpa only [Real.rpow_neg_one] using hc N period hN
  exact ActualRunAdmissionClock.flat_product
    (WardBin.hot R.family.path.levels m) hg (cost_nonnegative A m)
    hcost (hi N period hN) a c t he

private theorem forced_one (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (delta : ℝ) (hdelta : 0 < delta)
    (a c d t : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      cost A m ^ a *
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ (-(c : ℝ)) *
        Real.exp (-R.family.path.levels.clock.monitor m ^ delta /
          (1 + (R.family.path.levels.clock.coverSize m : ℝ)) ^ d) ≤
      Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ t := by
  filter_upwards [cost_subpower R A 1 zero_lt_one, actual_inverse_lower R A,
    forced_exponent R hG delta ((a + c + t : ℕ) : ℝ) hdelta (Nat.cast_nonneg _) d]
    with m hc hi he N period hN
  have hg := IterationFour.Currency.g_pos R.makes N period (m + 1)
    (Nat.succ_le_of_lt hN)
  have hcost : cost A m ≤
      (Pert.Asymptotics.regulatorRun R.family N period (m + 1))⁻¹ := by
    simpa only [Real.rpow_neg_one] using hc N period hN
  simpa only [neg_div] using ActualRunAdmissionClock.flat_product
    (g := Pert.Asymptotics.regulatorRun R.family N period (m + 1))
    (WardBin.hot R.family.path.levels m) hg (cost_nonnegative A m)
    hcost (hi N period hN) a c t he

private theorem price_le {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (m a c : ℕ) (g e : ℝ) (hg : 0 ≤ g) :
    cost A m ^ a * g ^ (-(c : ℝ)) * Real.exp e ≤
      A.admittedCost m ^ (2 * a) * g ^ (-(c : ℝ)) * Real.exp e :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (cost_power A m a) (Real.rpow_nonneg hg _))
    (Real.exp_pos _).le

private theorem regular_clipped (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (a c t : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      cost A m ^ a *
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ (-(c : ℝ)) *
        Real.exp (-min (A.pathRate m) 1 *
          (R.family.path.levels.clock.coverSize m : ℝ)) ≤
      Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ t := by
  obtain ⟨start, hstart⟩ := A.regular_flat (2 * a) c t
  filter_upwards [eventually_ge_atTop start, regular_one R hG A a c t]
    with m hm hone N period hN
  by_cases hr : A.pathRate m ≤ 1
  · rw [min_eq_left hr]
    exact (price_le A m a c _ _
      (IterationFour.Currency.g_pos R.makes N period (m + 1)
        (Nat.succ_le_of_lt hN)).le).trans (hstart m hm N period hN)
  · simpa only [min_eq_right (lt_of_not_ge hr).le, neg_one_mul] using hone N period hN

private theorem forced_clipped (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (delta : ℝ) (hdelta : 0 < delta)
    (a c d t : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      cost A m ^ a *
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ (-(c : ℝ)) *
        Real.exp (-min (A.pathRate m) 1 * R.family.path.levels.clock.monitor m ^ delta /
          (1 + (R.family.path.levels.clock.coverSize m : ℝ)) ^ d) ≤
      Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ t := by
  obtain ⟨start, hstart⟩ := A.forced_flat delta hdelta (2 * a) c d t
  filter_upwards [eventually_ge_atTop start, forced_one R hG A delta hdelta a c d t]
    with m hm hone N period hN
  by_cases hr : A.pathRate m ≤ 1
  · rw [min_eq_left hr]
    exact (price_le A m a c _ _
      (IterationFour.Currency.g_pos R.makes N period (m + 1)
        (Nat.succ_le_of_lt hN)).le).trans (hstart m hm N period hN)
  · simpa only [min_eq_right (lt_of_not_ge hr).le, neg_one_mul] using hone N period hN

/-- Choose the bounded input strip before selecting any F or M.
The bill doubles; all old norm, output-width, radius and calibration data stay. -/
def bounded (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) : NumericSchedule R.family J where
  inputNorm := A.inputNorm
  outputNorm := A.outputNorm
  input_norm := A.input_norm
  output_norm := A.output_norm
  inputWidth m := min (A.inputWidth m) 1
  outputWidth := A.outputWidth
  input_width_pos m := lt_min (A.input_width_pos m) zero_lt_one
  output_width_pos := A.output_width_pos
  admittedCost := cost A
  admitted_cost_nonnegative := cost_nonnegative A
  admitted_cost_ge_one m := (A.admitted_cost_ge_one m).trans (le_cost A m)
  radiusLoss := A.radiusLoss
  radius_loss_positive := A.radius_loss_positive
  radius_loss_ge_one := A.radius_loss_ge_one
  calibrationCap := A.calibrationCap
  calibration_cap_nonnegative := A.calibration_cap_nonnegative
  calibration_cap_tendsto := A.calibration_cap_tendsto
  cost_covers_widths m := by
    have hi := inverse_min_one (A.input_width_pos m)
    have hc := A.cost_covers_widths m
    have h1 := A.admitted_cost_ge_one m
    unfold cost
    linarith
  cost_covers_geometry m := (A.cost_covers_geometry m).trans (le_cost A m)
  cost_covers_units m N period hm := (A.cost_covers_units m N period hm).trans (le_cost A m)
  cost_subpower epsilon hepsilon := eventually_atTop.1 (cost_subpower R A epsilon hepsilon)
  pathRate m := min (A.pathRate m) 1
  path_rate_positive m := lt_min (A.path_rate_positive m) zero_lt_one
  path_rate_width m := le_min
    (le_min ((min_le_left _ _).trans ((A.path_rate_width m).trans (min_le_left _ _)))
      (min_le_right _ _))
    ((min_le_left _ _).trans ((A.path_rate_width m).trans (min_le_right _ _)))
  path_rate_cost m := by
    have hi := inverse_min_one (A.path_rate_positive m)
    have hc := A.path_rate_cost m
    have h1 := A.admitted_cost_ge_one m
    unfold cost
    linarith
  regular_flat a c t := eventually_atTop.1 (regular_clipped R hG A a c t)
  forced_flat delta hdelta a c d t :=
    eventually_atTop.1 (forced_clipped R hG A delta hdelta a c d t)

theorem input_width_le_one (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (m : ℕ) :
    (bounded R hG A).inputWidth m ≤ 1 := min_le_right _ _

theorem input_width_inverse (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (m : ℕ) :
    ((bounded R hG A).inputWidth m)⁻¹ = max (A.inputWidth m)⁻¹ 1 := by
  change (min (A.inputWidth m) 1)⁻¹ = _
  rcases le_total (A.inputWidth m) 1 with h | h
  · have hi : 1 ≤ (A.inputWidth m)⁻¹ := by
      simpa only [inv_one] using inv_anti₀ (A.input_width_pos m) h
    rw [min_eq_left h, max_eq_left hi]
  · have hi : (A.inputWidth m)⁻¹ ≤ 1 := by
      simpa only [inv_one] using inv_anti₀ zero_lt_one h
    rw [min_eq_right h, inv_one, max_eq_right hi]

theorem preserved (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) :
    (bounded R hG A).inputNorm = A.inputNorm ∧
      (bounded R hG A).outputNorm = A.outputNorm ∧
      (bounded R hG A).outputWidth = A.outputWidth ∧
      (bounded R hG A).radiusLoss = A.radiusLoss ∧
      (bounded R hG A).calibrationCap = A.calibrationCap := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem modified (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (m : ℕ) :
    (bounded R hG A).inputWidth m = min (A.inputWidth m) 1 ∧
      (bounded R hG A).pathRate m = min (A.pathRate m) 1 ∧
      (bounded R hG A).admittedCost m = 2 * A.admittedCost m := by
  exact ⟨rfl, rfl, rfl⟩

end YM.Integration.ActualBoundedNumericSchedule
end
