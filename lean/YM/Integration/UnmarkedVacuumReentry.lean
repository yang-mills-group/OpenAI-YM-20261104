import YM.Integration.UnmarkedVacuumLayerBudget
import YM.Integration.ActualCanonicalInputPayload
import YM.Integration.FullQLocalCanonicalForcedOutput
import YM.Integration.ActualNextLocalDatum

/-! Fixed-schedule reentry of the selected unmarked physical output. The next
input keeps the actual retuned masked list, regular reset, kinetic discrepancy
and every flagged native support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.UnmarkedVacuumReentry

open Lattice Wilson RG Marker RG3.Script.Picnic
open PhysicalNext.Repeat.Legato Comparison.RG02 IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Canonical
open scoped Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
    {d : LocalFormal.Datum R.family Γ} {caps : Handoff.OutputCapacities}
    {Y : Bulk.Chain R.family.path} {K : NumericPrices A} {F : AnalyticInput J A d}
    {η : ℝ} {I : FullPreparedInputAt F η} {M : AnalyticOutput caps Y K F}
    (S : Retained.Chosen K I M) (P : CanonicalOutput S)

/-- Given the canonical reset and its actual two physical bills, construct
the next complete vacuum preparation. The ambient source layout comes
from the same selected output, and both auxiliary marked costs are zero. -/
theorem atOutput (hJ : SameNorm J) {m : ℕ}
    (hm : d.level = m + 1)
    (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
    (field : Exterior.fieldDir G (R.family.side m d.period) 1)
    (F₁ : AnalyticInput J A (ActualNextLocalDatum.descend d hm W field))
    (hlayers : HEq F₁.layers (ActualRunRetunedVacuum.retunedLayers R M))
    (hpackets : F₁.packets = VacuumAuxiliaryInput.packets J.tests G _ Γ)
    (hroots : F₁.fineRoots = ActualNextLocalDatum.fineRoots F hm)
    (b : ℝ) (hb : b ≤ J.inheritedConstant *
      Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level ^
        ((J.order : ℝ) + 1 - J.eta))
    (E : Payload G (R.family.side d.level d.period))
    (hE : E.Invoice (A.inputNorm m) b)
    {η₁ : ℝ} (C : CalibrationPresentation P.output.carrier.rep (A.inputNorm m) η₁)
    (hExp : ∀ U, P.output.carrier.rep.exponent U = P.output.carrier.rep.scalar -
      ((R.family.path.rep d.cutoff d.period d.level).path.inChannels
        (R.family.path.levels.params d.level).clip P.output.carrier.rep.p
        (R.family.path.β d.cutoff d.period d.level) U +
        Render.renders (Render.prefactor (IterationFour.Currency.gain (M.plan.predict d.level)))
          P.output.carrier.rep.p U (M.plan.layers d.level)) -
      E.amount (A.inputNorm m) U - C.amount U)
    (hfine : I.carrier.rep.eval = (R.family.path.rep d.cutoff d.period (d.level+1)).eval) :
    ∃ I₁ : FullPreparedInputAt F₁ η₁, Retained.NativeIntake I₁ ∧
      HEq I₁.carrier P.output.carrier ∧ HEq I₁.error E ∧ HEq I₁.calibration C ∧
      I₁.inherited = b ∧ I₁.regularPrice = 0 ∧ I₁.forcedPrice = 0 ∧
      I₁.carrier.rep.eval = (R.family.path.rep d.cutoff d.period (m + 1)).eval := by
  rcases d with ⟨N, per, level, below, forest, tag, colors, field₀⟩
  dsimp only at hm
  subst level
  let x₀ := testInclusion J.tests (zeroIndependentTests J.tests)
  have hr : F₁.fineRoots = F.coarseRoots := hroots
  have hTemplate : ∃ T : Taste (TestSpace J.tests) F₁.fineRoots P.output.carrier.rep Γ,
      (T.leaf x₀).Active := by
    rw [hr]
    exact ⟨P.output.output, P.output_active x₀⟩
  obtain ⟨T, hT⟩ := hTemplate
  have hn := A.adjacent_norm hJ m
  have hwell : WellFormed (A.inputNorm m) P.output.carrier.rep := by
    rw [← hn]
    exact P.wellFormed
  have hreserved : P.output.carrier.rep.activities.KBound (A.inputNorm m)
      (R.family.path.levels.clock.forcedAllowance (m+1)) := by
    rw [← hn]
    exact P.fixed_forced
  have hclip : P.output.carrier.rep.clip = (R.family.path.levels.params (m+1)).clip := by
    rw [P.representation]
    rfl
  have hp : P.output.carrier.rep.p = R.family.path.levels.budget (m+1) := by
    rw [P.representation]
    rfl
  have hL : F₁.layers = ActualRunRetunedVacuum.retunedLayers R M := eq_of_heq hlayers
  let I₁ := VacuumAuxiliaryInput.atCarrier F₁ P.output.carrier hwell b hb E hE C
    (by
      intro U
      have h := hExp U
      have hrend := ActualRunRetunedVacuum.rendered R (M := M) U
      rw [← hp] at hrend
      rw [← hclip, ← hrend] at h
      rw [hL]
      exact h) T x₀ hT P.actual_forced hpackets
  exact ⟨I₁, ⟨P.actual_forced, hreserved, le_rfl, zero_le_one⟩,
    HEq.rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, P.output.output_vacuum R.makes below hfine⟩

/-- The only numerical input for restoring the selected vacuum layers is
their own graded cost at the next requested width. The original canonical
regular and kinetic bills are used separately on the same displayed field. -/
theorem step (hG : G.Simple) (hJ : SameNorm J) {m : ℕ}
    (hm : d.level = m + 1)
    (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
    (field : Exterior.fieldDir G (R.family.side m d.period) 1)
    (F₀ : AnalyticInput J A (ActualNextLocalDatum.descend d hm W field))
    (hroots : F₀.fineRoots = ActualNextLocalDatum.fineRoots F hm)
    (hFits : UnmarkedVacuumLayerBudget.Fits R M m)
    (hw : AnalyticBridge.VerifiedReset.Geo.Width (A.outputNorm d.level) (R.family.path.levels.params d.level).clip
      (R.family.path.levels.params d.level).width)
    (hb : ActualCanonicalInputPayload.errorPrice R I K ≤ J.inheritedConstant *
      Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level ^
        ((J.order : ℝ) + 1 - J.eta))
    {η₁ : ℝ} (C : CalibrationPresentation P.output.carrier.rep (A.inputNorm m) η₁)
    (hC : ∀ U, C.amount U =
      (P.output.carrier.rep.beta - R.family.path.β d.cutoff d.period d.level) *
      Push.BetaTransport.kinetic (R.family.path.rep d.cutoff d.period d.level).path
        (R.family.path.levels.params d.level).clip (A.inputNorm m) U)
    (hfine : I.carrier.rep.eval = (R.family.path.rep d.cutoff d.period (d.level+1)).eval) :
    ∃ F₁ : AnalyticInput J A (ActualNextLocalDatum.descend d hm W field),
    ∃ I₁ : FullPreparedInputAt F₁ η₁, Retained.NativeIntake I₁ ∧
      HEq I₁.carrier P.output.carrier ∧ HEq I₁.error (ActualCanonicalInputPayload.error R S) ∧
      HEq I₁.calibration C ∧ I₁.inherited = ActualCanonicalInputPayload.errorPrice R I K ∧
      I₁.regularPrice = 0 ∧ I₁.forcedPrice = 0 ∧
      I₁.carrier.rep.eval = (R.family.path.rep d.cutoff d.period (m+1)).eval ∧
      HEq F₁.layers (ActualRunRetunedVacuum.retunedLayers R M) ∧
      F₁.packets = VacuumAuxiliaryInput.packets J.tests G _ Γ ∧
      F₁.fineRoots = ActualNextLocalDatum.fineRoots F hm ∧ F₁.inputRegion = F₀.inputRegion := by
  rcases d with ⟨N, per, level, below, forest, tag, colors, field₀⟩
  dsimp only at hm
  subst level
  have hn := (A.adjacent_norm hJ m).symm
  let L := ActualRunRetunedVacuum.retunedLayers R M
  have hPaid : Render.permits L (A.inputNorm m) := by
    rw [hn]
    exact ActualRunRetunedVacuum.permits R (M := M)
  obtain ⟨H⟩ := hFits
  let F₁ := UnmarkedVacuumLayerBudget.input R F₀ L hPaid H
  have hData := UnmarkedVacuumLayerBudget.data R F₀ L hPaid H
  have hL : HEq F₁.layers (ActualRunRetunedVacuum.retunedLayers R M) :=
    heq_of_eq hData.1
  have hR : F₁.fineRoots = F.coarseRoots := hData.2.2.trans hroots
  have hi := ActualCanonicalInputPayload.invoice R S hG hw (A.inputNorm m)
    (congrArg BudgetPoint.threshold hn) (congrArg BudgetPoint.B hn)
    (le_of_eq (congrArg BudgetPoint.order hn)) (le_of_eq (congrArg BudgetPoint.power hn))
    (le_of_eq (congrArg BudgetPoint.supportExponent hn))
  have he := ActualCanonicalInputPayload.exponent R S P hG hw (A.inputNorm m)
    (congrArg BudgetPoint.threshold hn) C hC
  obtain ⟨I₁, hI, hcar, hE, hCal, hB, hReg, hFor, hAct⟩ :=
    atOutput R S P hJ rfl W field F₁ hL hData.2.1 hR _ hb _ hi C he hfine
  exact ⟨F₁, I₁, hI, hcar, hE, hCal, hB, hReg, hFor, hAct, hL, hData.2.1, hR, rfl⟩

end YM.Integration.UnmarkedVacuumReentry
