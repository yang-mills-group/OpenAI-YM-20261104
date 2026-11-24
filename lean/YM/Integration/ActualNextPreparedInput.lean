import YM.Integration.ActualNextAnalyticInput
import YM.Integration.ActualCanonicalInputPayload
import YM.Integration.ActualOrdinaryPriceMargins

/-!
Full physical preparation on the same canonical produced carrier.
The original marked output and all residual rows are used by prepareProduced.
The canonical affine-null error and full kinetic calibration remain separate;
every masked model layer is retained at the actual next coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualNextPreparedInput
open Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Canonical
open FullQLocal.PreRun.SuccessiveRequests
open scoped Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {Gamma : Census V} {J : Request V}
    (run : Run G) {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}
    {eta_w : ℝ} {I : FullPreparedInputAt F eta_w}
    {M : AnalyticOutput caps Y K F}
    (S : Retained.Chosen K I M) (P : CanonicalOutput S) (r : ℕ) {m : ℕ}
    (hm : datum.level = m + 1)
    (A' : NumericSchedule run.family (nextRequest J caps r))
    (W : Bulk.Colors Gamma G (run.family.side (m + 1) datum.period))
    (x : Exterior.fieldDir G (run.family.side m datum.period) 1)
    (width : ℕ → ℝ) (H : Prescribed.WidthReceipt width M)
    (hnorm : A'.inputNorm m = A.outputNorm datum.level)
    (hwidth : width datum.level = A'.inputWidth m)
    (hcost : (4 : ℝ)^J.order * K.geometry datum.level ≤ A'.admittedCost m)
    (hlo : (1/4 : ℝ) ≤ ActualRunRetunedVacuum.ratio run M)
    (hhi : ActualRunRetunedVacuum.ratio run M ≤ 4)
    (hpaid : (ActualRunInterpolatedPackets.onRun run datum.cutoff datum.period
        datum.level S.output.model r).Paid
      (A.outputNorm datum.level) F.outputAddresses M.region
      (fun v => F.outputRadii v / F.kernelCosts v)
      (Pert.Asymptotics.regulatorRun run.family datum.cutoff datum.period datum.level)
      (width datum.level) (K.geometry datum.level * 2) M.coverOffset M.coverSlope)
    (eligible : ActualNextAnalyticInput.Eligibility run.family J m)

local notation "F₁" => ActualNextAnalyticInput.build run S r hm A' W x width H
  hnorm hwidth hcost hlo hhi hpaid eligible

variable (hG : G.Simple)
    (hw : AnalyticBridge.VerifiedReset.Geo.Width (A.outputNorm datum.level)
      (run.family.path.levels.params datum.level).clip
      (run.family.path.levels.params datum.level).width)
    {eta_next : ℝ}
    (C : CalibrationPresentation P.output.carrier.rep (A'.inputNorm m) eta_next)
    (hC : ∀ U, C.amount U =
      (P.output.carrier.rep.beta -
        run.family.path.β datum.cutoff datum.period datum.level) *
      Push.BetaTransport.kinetic
        (run.family.path.rep datum.cutoff datum.period datum.level).path
        (run.family.path.levels.params datum.level).clip (A'.inputNorm m) U)
    (hInherited : ActualCanonicalInputPayload.errorPrice run I K ≤
      J.inheritedConstant *
        Pert.Asymptotics.regulatorRun run.family datum.cutoff datum.period datum.level ^
          ((J.order : ℝ) + 1 - J.eta))
    (q : ℕ) (hBounds : CanonicalBounds P 1 q)
    (hForced : Pert.Asymptotics.regulatorRun run.family datum.cutoff datum.period
      (datum.level + 1) ^ q ≤ J.forcedConstant)

/-- Complete next physical input, on the canonical output itself. -/
def input : FullPreparedInputAt F₁ eta_next := by
  rcases datum with ⟨N, period, level, below, forest, tag, colors, field⟩
  dsimp only at hm
  subst level
  have hInvoice := ActualCanonicalInputPayload.invoice run S hG hw (A'.inputNorm m)
    (congrArg BudgetPoint.threshold hnorm) (congrArg BudgetPoint.B hnorm)
    (le_of_eq (congrArg BudgetPoint.order hnorm))
    (le_of_eq (congrArg BudgetPoint.power hnorm))
    (le_of_eq (congrArg BudgetPoint.supportExponent hnorm))
  have hOldPaid : S.output.model.Paid (A.outputNorm (m + 1))
      F.outputAddresses M.region (fun v => F.outputRadii v / F.kernelCosts v)
      (Pert.Asymptotics.regulatorRun run.family N period (m + 1 + 1))
      (width (m + 1)) (K.geometry (m + 1)) M.coverOffset M.coverSlope := by
    rw [S.same_model]
    exact H.paid
  have hRead : ∀ y U,
      (ActualRunInterpolatedPackets.onRun run N period (m + 1) S.output.model r).read y
        (Pert.Asymptotics.regulatorRun run.family N period (m + 1)) U =
      P.output.model.read y
        (Pert.Asymptotics.regulatorRun run.family N period (m + 1 + 1)) U := by
    intro y U
    calc
      _ = S.output.model.read y
          (Pert.Asymptotics.regulatorRun run.family N period (m + 1 + 1)) U :=
        ActualRunInterpolatedPackets.onRun_read run N period (m + 1) below
          S.output.model r hOldPaid y U
      _ = _ := by rw [S.same_model, P.same_model]
  have hBudget : RelativeBudget (A'.inputNorm m)
      (pullback (testInclusion J.tests) P.output.residual) F.outputRadii
      (forcedDivisor run.family (m + 1)) (envelopeProduct F.kernelCosts)
      (Retained.ordinaryRate K I 1)
      (Pert.Asymptotics.regulatorRun run.family N period (m + 1 + 1) ^ q) := by
    rw [hnorm]
    exact hBounds.residual_price
  exact {
    carrier := P.output.carrier
    wellFormed := by
      change WellFormed (A'.inputNorm m) P.output.carrier.rep
      rw [hnorm]
      exact P.wellFormed
    inherited := ActualCanonicalInputPayload.errorPrice run I K
    inherited_nonnegative := IterationFour.Vacuum.Payload.nonneg hInvoice
    inherited_bound := hInherited
    error := ActualCanonicalInputPayload.error run S
    error_paid := hInvoice
    calibration := C
    exponent := fun U => by
      have he := ActualCanonicalInputPayload.exponent run S P hG hw (A'.inputNorm m)
        (congrArg BudgetPoint.threshold hnorm) C hC U
      have hclip : P.output.carrier.rep.clip =
          (run.family.path.levels.params (m + 1)).clip := by
        rw [P.representation]
        rfl
      have hp : P.output.carrier.rep.p = run.family.path.levels.budget (m + 1) := by
        rw [P.representation]
        rfl
      have hr := ActualRunRetunedVacuum.rendered run (M := M) U
      rw [← hp] at hr
      rw [← hclip, ← hr] at he
      exact he
    input := P.output.output
    multilinear := P.output_multilinear
    input_retains := P.output_retains
    regularPrice := Retained.ordinaryRate K I 1
    forcedPrice := Pert.Asymptotics.regulatorRun run.family N period (m + 1 + 1) ^ q
    forced_bound := hForced
    prepared := prepareProduced P.output (A'.inputNorm m)
      (S.onRun_retuned_layer_colors r)
      (ActualRunInterpolatedPackets.onRun run N period (m + 1) S.output.model r)
      F.outputRadii F.kernelCosts (Retained.ordinaryRate K I 1)
      (Pert.Asymptotics.regulatorRun run.family N period (m + 1 + 1) ^ q)
      (S.onRun_retuned_layer_input r) hRead hBudget }

local notation "I₁" => input run S P r hm A' W x width H hnorm hwidth hcost
  hlo hhi hpaid eligible hG hw C hC hInherited q hBounds hForced

/-- The literal prices used by the inherited and ordinary recurrences. -/
theorem prices :
    (I₁).inherited = ActualCanonicalInputPayload.errorPrice run I K ∧
    (I₁).regularPrice = Retained.ordinaryRate K I 1 ∧
    (I₁).forcedPrice =
      Pert.Asymptotics.regulatorRun run.family datum.cutoff datum.period
        (datum.level + 1) ^ q := by
  rcases datum with ⟨N, period, level, below, forest, tag, colors, field⟩
  dsimp only at hm
  subst level
  exact ⟨rfl, rfl, rfl⟩

/-- Both original forced allowances transfer on the same canonical carrier.
Ordinary smallness is exactly the previously proved recurrence duty. -/
theorem native_intake (heta : 0 ≤ eta_w) (hI : Retained.NativeIntake I)
    (hordinary : Retained.ordinaryRate K I 1 ≤ 1) :
    Retained.NativeIntake I₁ := by
  rcases datum with ⟨N, period, level, below, forest, tag, colors, field⟩
  dsimp only at hm
  subst level
  refine {
    original := P.actual_forced
    reserved := ?_
    ordinary_nonnegative := ?_
    ordinary_small := hordinary }
  · change P.output.carrier.rep.activities.KBound (A'.inputNorm m)
      (run.family.path.levels.clock.forcedAllowance (m + 1))
    rw [hnorm]
    exact P.fixed_forced
  · change 0 ≤ Retained.ordinaryRate K I 1
    rw [← ActualOrdinaryPriceMargins.rate_eq run K I]
    exact ActualOrdinaryPriceMargins.rate_nonnegative run K N period (m + 1)
      I.inherited eta_w I.regularPrice I.inherited_nonnegative heta hI.ordinary_nonnegative

/-- The constructed next carrier retains the exact original physical law. -/
theorem actual_eval
    (hFine : I.carrier.rep.eval =
      (run.family.path.rep datum.cutoff datum.period (datum.level + 1)).eval) :
    (I₁).carrier.rep.eval =
      (run.family.path.rep datum.cutoff datum.period (m + 1)).eval := by
  rcases datum with ⟨N, period, level, below, forest, tag, colors, field⟩
  dsimp only at hm
  subst level
  change P.output.carrier.rep.eval =
    (run.family.path.rep N period (m + 1)).eval
  exact P.output.output_vacuum run.makes below hFine

end YM.Integration.ActualNextPreparedInput
end
