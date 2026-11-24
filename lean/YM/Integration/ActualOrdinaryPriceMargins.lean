import YM.Integration.FullQLocalRetainedGrant
import YM.Integration.FullQLocalNumericMarkedRateBound
import YM.Integration.ActualRunAdjacentCoupling

/-! The full ordinary marked bill preserves every positive power margin
strictly below two at each fixed stage. The original polynomial coefficient
is retained; no single tail uniform over all stages is asserted. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualOrdinaryPriceMargins
open Filter Lattice RG LocalComparison
open PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}
    (R : Run G) {A : NumericSchedule R.family J} (K : NumericPrices A)

/-- Exactly the fresh marked rate plus the old distinguished rough bill. -/
def rate (N period m : ℕ) (inherited calibration regular : ℝ) : ℝ :=
  markedRate J.order 1 (K.markedConstant 1) (K.geometry m)
    inherited calibration
    (Pert.Asymptotics.regulatorRun R.family N period (m + 1)) +
  K.geometry m * regular

theorem rate_nonnegative (N period m : ℕ) (inherited calibration regular : ℝ)
    (hi : 0 ≤ inherited) (hc : 0 ≤ calibration) (hr : 0 ≤ regular) :
    0 ≤ rate R K N period m inherited calibration regular := by
  unfold rate markedRate
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (K.marked_constant_nonnegative 1 zero_lt_one)
        (Real.rpow_nonneg (by unfold Pert.Asymptotics.regulatorRun; positivity) _))
      (mul_nonneg (K.geometry_nonnegative m) (add_nonneg hi hc)))
    (mul_nonneg (K.geometry_nonnegative m) hr)

/-- Each exponent has its own tail, before every cutoff and admitted period. -/
def PowerMargins (price : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 2 →
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      J.physicalPeriodLower ≤ (R.family.S.period period).val →
      price N period m ≤
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ t

theorem zero_margins :
    PowerMargins (J := J) R (fun _ _ _ => 0) := by
  intro t _ _
  filter_upwards [] with m N period hN _
  exact Real.rpow_nonneg
    (IterationFour.Currency.g_pos R.makes N period (m + 1) (by omega)).le t

private theorem power_payment (hG : G.Simple) (c k s : ℝ)
    (hc : 0 ≤ c) (hk : 0 < k) (hs : 0 < s) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      c * Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ s ≤ k := by
  have htwo : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  obtain ⟨start, hstart⟩ := eventually_atTop.1
    (IterationFour.Currency.buy R.family.path.levels hG c
      (k := k / (2 : ℝ) ^ s) (div_pos hk htwo) (s := 0) (t := s) hs)
  filter_upwards [eventually_ge_atTop start] with m hm N period hN
  have hpaid : c * IterationFour.Currency.weight R.family.path.levels s (m + 1) ≤
      k / (2 : ℝ) ^ s := by
    simpa only [IterationFour.Currency.weight, Real.rpow_zero, mul_one] using
      hstart (m + 1) (by omega)
  calc
    _ ≤ c * ((2 : ℝ) ^ s *
        IterationFour.Currency.weight R.family.path.levels s (m + 1)) :=
      mul_le_mul_of_nonneg_left
        (IterationFour.Currency.g_weight R.makes
          (N := N) (q := period) (i := m + 1) (by omega) s hs.le).2 hc
    _ = (2 : ℝ) ^ s *
        (c * IterationFour.Currency.weight R.family.path.levels s (m + 1)) := by ring
    _ ≤ (2 : ℝ) ^ s * (k / (2 : ℝ) ^ s) :=
      mul_le_mul_of_nonneg_left hpaid htwo.le
    _ = k := by rw [mul_comm, div_mul_cancel₀ _ htwo.ne']

/-- A strictly stronger old margin pays both the original geometry factor and
the actual adjacent-coupling conversion. Every input scalar remains explicit. -/
theorem step (hG : G.Simple) (t : ℝ) (ht : 0 < t) (ht2 : t < 2) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      ∀ inherited calibration regular : ℝ,
      inherited ≤ J.inheritedConstant *
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^
          ((J.order : ℝ) + 1 - J.eta) →
      calibration ≤ Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ 3 →
      regular ≤ Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^
        ((t + 2) / 2) →
      rate R K N period m inherited calibration regular ≤
        Pert.Asymptotics.regulatorRun R.family N period m ^ t := by
  let epsilon : ℝ := (2 - t) / 4
  let c : ℝ := K.markedConstant 1 + J.inheritedConstant + 1
  let k : ℝ := (2 : ℝ) ^ (-t) / 2
  have hepsilon : 0 < epsilon := div_pos (sub_pos.mpr ht2) (by norm_num)
  have hc : 0 ≤ c := by
    dsimp [c]
    linarith [K.marked_constant_nonnegative 1 zero_lt_one,
      J.inherited_constant_nonnegative]
  have hk : 0 < k := div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
  obtain ⟨start, hgeometry⟩ := K.subpower epsilon hepsilon
  filter_upwards [K.eventually_markedRate_square hG R.makes,
    ActualRunAdjacentCoupling.eventually_ratio R hG,
    power_payment R hG c k (2 - t) hc hk (sub_pos.mpr ht2),
    power_payment R hG 1 k epsilon zero_le_one hk hepsilon,
    eventually_ge_atTop start] with m hmarked hratio hfresh hmargin hm N period hN
  intro inherited calibration regular hi hcal hr
  let g := Pert.Asymptotics.regulatorRun R.family N period (m + 1)
  let g0 := Pert.Asymptotics.regulatorRun R.family N period m
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N period (m + 1) (by omega)
  have hg0 : 0 < g0 := IterationFour.Currency.g_pos R.makes N period m hN.le
  have hK : K.geometry m ≤ g ^ (-epsilon) := hgeometry m hm N period hN
  have hnew : markedRate J.order 1 (K.markedConstant 1) (K.geometry m)
      inherited calibration g ≤ k * g ^ t := by
    calc
      _ ≤ c * g ^ 2 := hmarked N period hN inherited calibration hi hcal
      _ = (c * g ^ (2 - t)) * g ^ t := by
        rw [mul_assoc, ← Real.rpow_add hg, sub_add_cancel, Real.rpow_two]
      _ ≤ k * g ^ t :=
        mul_le_mul_of_nonneg_right (hfresh N period hN) (Real.rpow_nonneg hg.le t)
  have hold : K.geometry m * regular ≤ k * g ^ t := by
    calc
      _ ≤ K.geometry m * g ^ ((t + 2) / 2) :=
        mul_le_mul_of_nonneg_left hr (K.geometry_nonnegative m)
      _ ≤ g ^ (-epsilon) * g ^ ((t + 2) / 2) :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hg.le _)
      _ = g ^ epsilon * g ^ t := by
        rw [← Real.rpow_add hg, ← Real.rpow_add hg]
        congr 1
        dsimp [epsilon]
        ring
      _ ≤ k * g ^ t :=
        mul_le_mul_of_nonneg_right
          (by simpa only [one_mul] using hmargin N period hN)
          (Real.rpow_nonneg hg.le t)
  have hadj : g ≤ 2 * g0 := (div_le_iff₀ hg0).mp (hratio N period hN).2
  calc
    rate R K N period m inherited calibration regular ≤ k * g ^ t + k * g ^ t :=
      add_le_add hnew hold
    _ = (2 : ℝ) ^ (-t) * g ^ t := by dsimp [k]; ring
    _ ≤ (2 : ℝ) ^ (-t) * (2 * g0) ^ t :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hg.le hadj ht.le) (Real.rpow_nonneg (by norm_num) _)
    _ = g0 ^ t := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hg0.le,
        ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        neg_add_cancel, Real.rpow_zero, one_mul]

/-- Zero at the no-prior-step boundary; otherwise the literal full old rate. -/
def descendedRate (inherited calibration regular : ℕ → ℕ → ℕ → ℝ)
    (N period m : ℕ) : ℝ :=
  if m + 1 < N then
    rate R K N period (m + 1)
      (inherited N period (m + 1)) (calibration N period (m + 1))
      (regular N period (m + 1))
  else 0

theorem margins_step (hG : G.Simple)
    (inherited calibration regular : ℕ → ℕ → ℕ → ℝ)
    (hi : ∀ N period m, m < N →
      J.physicalPeriodLower ≤ (R.family.S.period period).val →
      inherited N period m ≤ J.inheritedConstant *
        Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^
          ((J.order : ℝ) + 1 - J.eta))
    (hcal : Retained.UniformlyFlat (C := R.family) J calibration)
    (hr : PowerMargins (J := J) R regular) :
    PowerMargins (J := J) R (descendedRate R K inherited calibration regular) := by
  intro t ht ht2
  have hu : 0 < (t + 2) / 2 := by linarith
  have hu2 : (t + 2) / 2 < 2 := by linarith
  obtain ⟨first, hfirst⟩ := hcal.2 3
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (step R K hG t ht ht2),
    (tendsto_add_atTop_nat 1).eventually (hr ((t + 2) / 2) hu hu2),
    eventually_ge_atTop first] with m hstep hregular hm N period hN hp
  by_cases hprior : m + 1 < N
  · rw [descendedRate, if_pos hprior]
    exact hstep N period hprior _ _ _
      (hi N period (m + 1) hprior hp)
      (hfirst N period (m + 1) (by omega) hprior hp)
      (hregular N period hprior hp)
  · rw [descendedRate, if_neg hprior]
    exact Real.rpow_nonneg
      (IterationFour.Currency.g_pos R.makes N period (m + 1) (by omega)).le t

theorem margins_small (hG : G.Simple) (price : ℕ → ℕ → ℕ → ℝ)
    (hp : PowerMargins (J := J) R price) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      J.physicalPeriodLower ≤ (R.family.S.period period).val → price N period m ≤ 1 := by
  obtain ⟨first, hfirst⟩ := eventually_atTop.1
    (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one)
  filter_upwards [hp 1 zero_lt_one (by norm_num),
    eventually_ge_atTop first] with m hm hstart N period hN hperiod
  have h := hm N period hN hperiod
  rw [Real.rpow_one] at h
  exact h.trans (hfirst (m + 1) (by omega) N period (by omega)).le

section Actual
variable [DecidableEq V] [Fintype V] {Gamma : Marker.Census V}
    {datum : LocalFormal.Datum R.family Gamma}
    {F : AnalyticInput J A datum} {eta : ℝ}

theorem rate_eq (I : FullPreparedInputAt F eta) :
    rate R K datum.cutoff datum.period datum.level
      I.inherited eta I.regularPrice = Retained.ordinaryRate K I 1 := rfl

end Actual
end YM.Integration.ActualOrdinaryPriceMargins
end
