import YM.Integration.ActualCanonicalInputPayload
import YM.Integration.ActualCappedRegularPayment

/-! Pointwise growth of the complete canonical regular remainder.
The original source price is retained as a factor. The cost below is the
native admission cost, whose actual width and path receipts are available. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCanonicalPayloadPrice
open Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato
open ActualRunAdmissionScales
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped BigOperators

variable {G : Gauge}

def coefficient (G : Gauge) (p : BudgetPoint) : Real :=
  2 * CappedRegularGrowth.coefficient G p *
    (3 : Real) ^ CappedRegularGrowth.degree p

def degree (p : BudgetPoint) : Nat := CappedRegularGrowth.degree p + 2

theorem coefficient_positive (G : Gauge) (p : BudgetPoint) :
    0 < coefficient G p := by
  have h := CappedRegularGrowth.coefficient_positive G p
  unfold coefficient
  positivity

private lemma profile_cost (A : Levels G) (m : ℕ) :
    (A.params m).width⁻¹ ≤ admittedCost A m ∧
      (A.params m).paths ≤ admittedCost A m := by
  have hp := inv_pos.mpr (pairWidth_pos A m)
  have hw := inv_anti₀ (pairWidth_pos A m)
    (show pairWidth A m ≤ (A.params m).width from min_le_right _ _)
  have hgeo := geometryCost_nonneg A m
  have hu := unitCost_nonneg A m
  have hbase : (pairWidth A m)⁻¹ ≤ admittedCost A m := by
    unfold admittedCost
    linarith
  refine ⟨hw.trans hbase, ?_⟩
  apply le_trans ?_ (cost_covers_geometry A m)
  have hpf := (A.params (m+1)).paths_pos
  have hc := (A.params m).columns_ge
  have hcf := (A.params (m+1)).columns_ge
  have hr := (A.params m).clip.radius_pos
  have hrf := (A.params (m+1)).clip.radius_pos
  have hm : 0 < A.clock.monitor m := Real.exp_pos _
  have hmf : 0 < A.clock.monitor (m+1) := Real.exp_pos _
  have hl := Real.rpow_nonneg hm.le (A.clock.theta (A.clock.J m))
  have hlf := Real.rpow_nonneg hmf.le (A.clock.theta (A.clock.J (m+1)))
  unfold geometryCost Calendar.loopCap
  linarith [Nat.cast_nonneg (α := ℝ) (A.clock.coverSize m),
    Nat.cast_nonneg (α := ℝ) (A.clock.coverSize (m+1))]


private theorem regular_need (A : Levels G) (m : Nat) (p q : BudgetPoint)
    (hp : p.power = q.power) (ho : p.order = q.order)
    (hs : p.supportExponent = q.supportExponent)
    (P : PathData G) (Lambda H : Real)
    (hP : P.Bounds (A.params m).clip (A.params m).width
      (A.params m).paths Lambda) (hH : 0 ≤ H) :
    CappedRegularReset.regularNeed G p (A.params m).clip
      (A.params m).width (A.params m).paths 0 H ≤
      coefficient G q * admittedCost A m ^ degree q * H := by
  let a := admittedCost A m
  let D := CappedRegularGrowth.degree q
  have ha1 : 1 ≤ a := admittedCost_one A m
  have ha : 0 ≤ a := zero_le_one.trans ha1
  obtain ⟨hw, hc⟩ := profile_cost A m
  have hw0 := inv_pos.mpr (A.params m).width_pos
  have hc0 := (A.params m).paths_pos
  have hcoef := CappedRegularGrowth.coefficient_positive G q
  have hw' : 1 + 2 * (A.params m).width⁻¹ ≤ 3*a := by
    change (A.params m).width⁻¹ ≤ a at hw
    linarith
  have hc' : 1 + (A.params m).paths^2 ≤ 2*a^2 := by
    have hsq := pow_le_pow_left₀ hc0.le hc 2
    have ha2 : 1 ≤ a^2 := one_le_pow₀ ha1
    change (A.params m).paths^2 ≤ a^2 at hsq
    linarith
  rw [CappedRegularGrowth.regular_fields G p q (A.params m).clip
    (A.params m).width (A.params m).paths H hp ho hs]
  calc
    _ ≤ CappedRegularGrowth.coefficient G q *
        (1 + 2 * (A.params m).width⁻¹)^D * (1 + (A.params m).paths^2) * H :=
      CappedRegularGrowth.regular_growth G q (A.params m).clip
        (A.params m).width_pos hc0.le hH (ActualCappedRegularPayment.direct_le_one hP)
    _ ≤ CappedRegularGrowth.coefficient G q * (3*a)^D * (2*a^2) * H := by
      apply mul_le_mul_of_nonneg_right ?_ hH
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw' D) hcoef.le)
        hc' (by positivity) (by positivity)
    _ = coefficient G q * admittedCost A m ^ degree q * H := by
      dsimp only [coefficient, degree, D, a]
      rw [mul_pow, pow_add (admittedCost A m) (CappedRegularGrowth.degree q) 2]
      ring

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
theorem price (S : Retained.Chosen K I M) :
    ActualCanonicalInputPayload.errorPrice run I K ≤
      coefficient G (A.outputNorm 0) *
        admittedCost run.family.path.levels datum.level ^ degree (A.outputNorm 0) *
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
  exact regular_need run.family.path.levels datum.level
    (A.outputNorm datum.level) (A.outputNorm 0)
    (hp.trans hp0.symm) (ho.trans ho0.symm) (hs.trans hs0.symm) P
    (run.family.path.levels.clock.loopCap datum.level)
    (ActualSelectedVacuumGerm.sourcePrice run I K) hP S.vacuum.estimate.H_nonneg

end Actual
end YM.Integration.ActualCanonicalPayloadPrice
end
