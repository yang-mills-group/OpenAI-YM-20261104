import YM.Integration.FullQLocalRetainedGrant

/-!
Pointwise full residual envelopes for the current retained grant.
The chosen carrier's exponent and every nonempty flag remain literal.
The second consequence retains the full model factor. These raw bounds
do not assert a uniform normalized error or an integrated tail payment.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G}
    {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {S : Chosen K I M} {delta : ℝ} {forcedOrder : ℕ}

/-- The all-field raw bound keeps both the ordinary error and the complete
flagged exponential background. No division by the vacuum is performed. -/
theorem Bounds.residual_density_error_price (H : Bounds S delta forcedOrder)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
          forcedOrder) ≤ 1)
    (x : IndependentTests J.tests) (U : Config G (C.side datum.level datum.period)) :
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)
    let e := ordinaryRate K I delta
    Poly.price (fun v => F.outputRadii v / F.kernelCosts v)
      ((S.output.residual.leaf (testInclusion J.tests x)).density U -
        (S.output.carrier.rep.eval U : ℂ) • (1 : Poly B)) ≤
      |S.output.carrier.rep.eval U| * (Real.exp (Fintype.card V * e) - 1) +
      (Real.exp (S.output.carrier.rep.exponent U) * Real.exp (Fintype.card V * e)) *
        (if flags S.output.carrier.rep.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (forcedDivisor C datum.level * g ^ forcedOrder)) *
            Real.exp (-SectorNext.Vacuum.flagRate (A.outputNorm datum.level) *
              (flags S.output.carrier.rep.p.threshold U).card)) := by
  exact PreResetDensity.full_density_error_price H.residual_price F.kernel_positive
    ((A.output_norm datum.level).threshold.trans
      (congrArg BudgetPoint.threshold S.output.carrier.point).symm)
    S.fixed_forced hSmall x U

/-- Multiply the exact raw residual by the same complete selected model.
A later same-scene argument may integrate this bound; no such estimate or
uniform control of the flagged ratio is inferred here. -/
theorem Bounds.full_model_defect_price (H : Bounds S delta forcedOrder)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) ^
          forcedOrder) ≤ 1)
    (x : IndependentTests J.tests) (U : Config G (C.side datum.level datum.period)) :
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)
    let e := ordinaryRate K I delta
    Poly.price (fun v => F.outputRadii v / F.kernelCosts v)
      ((S.output.output.leaf (testInclusion J.tests x)).density U -
        (S.output.carrier.rep.eval U : ℂ) •
          S.output.modelValue (testInclusion J.tests x) U) ≤
      Poly.price (fun v => F.outputRadii v / F.kernelCosts v)
        (S.output.modelValue (testInclusion J.tests x) U) *
      (|S.output.carrier.rep.eval U| * (Real.exp (Fintype.card V * e) - 1) +
        (Real.exp (S.output.carrier.rep.exponent U) * Real.exp (Fintype.card V * e)) *
          (if flags S.output.carrier.rep.p.threshold U = ∅ then 0 else
            ((Fintype.card V : ℝ) * (forcedDivisor C datum.level * g ^ forcedOrder)) *
              Real.exp (-SectorNext.Vacuum.flagRate (A.outputNorm datum.level) *
                (flags S.output.carrier.rep.p.threshold U).card))) := by
  have hw : ∀ v, 0 < F.outputRadii v / F.kernelCosts v :=
    fun v => div_pos (F.output_radius_positive v) (F.kernel_positive v)
  have hfactor :
      (S.output.output.leaf (testInclusion J.tests x)).density U -
          (S.output.carrier.rep.eval U : ℂ) •
            S.output.modelValue (testInclusion J.tests x) U =
        S.output.modelValue (testInclusion J.tests x) U *
          ((S.output.residual.leaf (testInclusion J.tests x)).density U -
            (S.output.carrier.rep.eval U : ℂ) • (1 : Poly B)) := by
    simp only [S.output.full, ProducedOutput.modelValue, mul_sub, mul_smul_comm,
      mul_one]
  rw [hfactor]
  exact (Poly.multiplication hw _ _).trans
    (mul_le_mul_of_nonneg_left (H.residual_density_error_price hSmall x U)
      (Poly.nonnegative hw _))

end YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
end
