import YM.Integration.ActualCanonicalPayloadPrice

/-! The same full canonical regular remainder is priced by the supplied
NumericSchedule. Its native width is already paid through slow_selector
and the existing clip-relaxation term of cost_covers_geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCanonicalPayloadPrice
open Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped BigOperators

variable {G : Gauge}

section Numerical
variable {V : Type} {J : Request V}

private theorem scheduled_profile_cost (run : Run G)
    (A : NumericSchedule run.family J) (m : ℕ) :
    ((run.family.path.levels.params m).width)⁻¹ ≤ A.admittedCost m ∧
      (run.family.path.levels.params m).paths ≤ A.admittedCost m := by
  have h := A.cost_covers_geometry m
  have hb0 : 0 ≤ (run.family.path.levels.clock.coverSize m : ℝ) := Nat.cast_nonneg _
  have hb1 : 0 ≤ (run.family.path.levels.clock.coverSize (m + 1) : ℝ) := Nat.cast_nonneg _
  have hm (i : ℕ) : 0 ≤ run.family.path.levels.clock.monitor i := by
    unfold Calendar.monitor
    positivity
  have hl (i : ℕ) : 0 ≤ run.family.path.levels.clock.loopCap i := by
    unfold Calendar.loopCap
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hm i) _)
  have hp0 := (run.family.path.levels.params m).paths_pos.le
  have hp1 := (run.family.path.levels.params (m + 1)).paths_pos.le
  have hc0 := (run.family.path.levels.params m).columns_ge
  have hc1 := (run.family.path.levels.params (m + 1)).columns_ge
  have hr0 := (run.family.path.levels.params m).clip.radius_pos.le
  have hr1 := (run.family.path.levels.params (m + 1)).clip.radius_pos.le
  have hm0 := hm m
  have hm1 := hm (m + 1)
  have hl0 := hl m
  have hl1 := hl (m + 1)
  have hrel : (run.family.path.levels.params m).clip.relaxation ≤ A.admittedCost m := by
    linarith
  have hi : ((run.family.path.levels.params m).width)⁻¹ ≤
      (run.family.path.levels.params m).clip.relaxation := by
    rw [← one_div]
    apply (div_le_iff₀ (run.family.path.levels.params m).width_pos).mpr
    linarith [(run.family.path.levels.params m).slow_selector]
  exact ⟨hi.trans hrel, by linarith⟩

private theorem scheduled_regular_need (run : Run G)
    (A : NumericSchedule run.family J) (m : Nat) (p q : BudgetPoint)
    (hp : p.power = q.power) (ho : p.order = q.order)
    (hs : p.supportExponent = q.supportExponent)
    (P : PathData G) (Lambda H : Real)
    (hP : P.Bounds (run.family.path.levels.params m).clip (run.family.path.levels.params m).width
      (run.family.path.levels.params m).paths Lambda) (hH : 0 ≤ H) :
    CappedRegularReset.regularNeed G p (run.family.path.levels.params m).clip
      (run.family.path.levels.params m).width (run.family.path.levels.params m).paths 0 H ≤
      coefficient G q * A.admittedCost m ^ degree q * H := by
  let a := A.admittedCost m
  let D := CappedRegularGrowth.degree q
  have ha1 : 1 ≤ a := A.admitted_cost_ge_one m
  have ha : 0 ≤ a := zero_le_one.trans ha1
  obtain ⟨hw, hc⟩ := scheduled_profile_cost run A m
  have hw0 := inv_pos.mpr (run.family.path.levels.params m).width_pos
  have hc0 := (run.family.path.levels.params m).paths_pos
  have hcoef := CappedRegularGrowth.coefficient_positive G q
  have hw' : 1 + 2 * (run.family.path.levels.params m).width⁻¹ ≤ 3*a := by
    change (run.family.path.levels.params m).width⁻¹ ≤ a at hw
    linarith
  have hc' : 1 + (run.family.path.levels.params m).paths^2 ≤ 2*a^2 := by
    have hsq := pow_le_pow_left₀ hc0.le hc 2
    have ha2 : 1 ≤ a^2 := one_le_pow₀ ha1
    change (run.family.path.levels.params m).paths^2 ≤ a^2 at hsq
    linarith
  rw [CappedRegularGrowth.regular_fields G p q (run.family.path.levels.params m).clip
    (run.family.path.levels.params m).width (run.family.path.levels.params m).paths H hp ho hs]
  calc
    _ ≤ CappedRegularGrowth.coefficient G q *
        (1 + 2 * (run.family.path.levels.params m).width⁻¹)^D * (1 + (run.family.path.levels.params m).paths^2) * H :=
      CappedRegularGrowth.regular_growth G q (run.family.path.levels.params m).clip
        (run.family.path.levels.params m).width_pos hc0.le hH (ActualCappedRegularPayment.direct_le_one hP)
    _ ≤ CappedRegularGrowth.coefficient G q * (3*a)^D * (2*a^2) * H := by
      apply mul_le_mul_of_nonneg_right ?_ hH
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw' D) hcoef.le)
        hc' (by positivity) (by positivity)
    _ = coefficient G q * A.admittedCost m ^ degree q * H := by
      dsimp only [coefficient, degree, D, a]
      rw [mul_pow, pow_add (A.admittedCost m) (CappedRegularGrowth.degree q) 2]
      ring

/-- The extraction multiplier alone, with no selected output or remainder
in the statement. The original path at one fixed cutoff supplies the clip bound. -/
theorem scheduled_factor (run : Run G)
    (A : NumericSchedule run.family J) (m : ℕ) :
    CappedRegularReset.regularNeed G (A.outputNorm m)
      (run.family.path.levels.params m).clip
      (run.family.path.levels.params m).width
      (run.family.path.levels.params m).paths 0 1 ≤
      coefficient G (A.outputNorm 0) *
        A.admittedCost m ^ degree (A.outputNorm 0) := by
  let P := (run.family.path.rep (m + 1) 0 m).path
  have hP : P.Bounds (run.family.path.levels.params m).clip
      (run.family.path.levels.params m).width
      (run.family.path.levels.params m).paths
      (run.family.path.levels.clock.loopCap m) := by
    have h : run.family.path.Conv (m + 1) 0 m :=
      run.makes.wilson.represents (m + 1) 0 m (Nat.le_succ m)
    rw [← h.clip]
    exact h.good.paths
  obtain ⟨_, _, ho, hp, hs⟩ := A.output_norm m
  obtain ⟨_, _, ho0, hp0, hs0⟩ := A.output_norm 0
  simpa only [mul_one] using scheduled_regular_need run A m
    (A.outputNorm m) (A.outputNorm 0)
    (hp.trans hp0.symm) (ho.trans ho0.symm) (hs.trans hs0.symm) P
    (run.family.path.levels.clock.loopCap m) 1 hP zero_le_one

end Numerical

section Actual
variable (run : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities}
    {Y : YM.Comparison.RG02.Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : Real}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}

/-- The fixed coefficient and degree precede every stage, cutoff, period
and selected output. No old inherited or calibration term is discarded. -/
theorem scheduled_price (S : Retained.Chosen K I M) :
    ActualCanonicalInputPayload.errorPrice run I K ≤
      coefficient G (A.outputNorm 0) *
        A.admittedCost datum.level ^ degree (A.outputNorm 0) *
        ActualSelectedVacuumGerm.sourcePrice run I K := by
  let P := (run.family.path.rep datum.cutoff datum.period datum.level).path
  have hP : P.Bounds (run.family.path.levels.params datum.level).clip
      (run.family.path.levels.params datum.level).width
      (run.family.path.levels.params datum.level).paths
      (run.family.path.levels.clock.loopCap datum.level) := by
    have h : run.family.path.Conv datum.cutoff datum.period datum.level :=
      run.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le
    rw [← h.clip]
    exact h.good.paths
  obtain ⟨_, _, ho, hp, hs⟩ := A.output_norm datum.level
  obtain ⟨_, _, ho0, hp0, hs0⟩ := A.output_norm 0
  exact scheduled_regular_need run A datum.level
    (A.outputNorm datum.level) (A.outputNorm 0)
    (hp.trans hp0.symm) (ho.trans ho0.symm) (hs.trans hs0.symm) P
    (run.family.path.levels.clock.loopCap datum.level)
    (ActualSelectedVacuumGerm.sourcePrice run I K) hP S.vacuum.estimate.H_nonneg

end Actual
end YM.Integration.ActualCanonicalPayloadPrice
end
