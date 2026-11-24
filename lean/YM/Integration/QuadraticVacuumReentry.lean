import YM.Integration.QuadraticVacuumAnalytic
import YM.Integration.FullQLocalCanonicalForcedOutput
import YM.Integration.ActualNextLocalDatum

/-! Reentry of the canonical quadratic vacuum on the identical fixed
schedule. Each step keeps every native forced row of the produced
representation. Its affine-null error and full kinetic calibration have
separate certificates in the same requested norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QuadraticVacuumReentry

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
theorem atOutput (horder : J.order = 2) (hJ : SameNorm J) {m : ℕ}
    (hm : d.level = m + 1)
    (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
    (field : Exterior.fieldDir G (R.family.side m d.period) 1)
    (F₁ : AnalyticInput J A (ActualNextLocalDatum.descend d hm W field))
    (hlayers : F₁.layers = [])
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
  have hnil : M.plan.layers (m+1) = [] :=
    QuadraticVacuumAnalytic.selected_layers R J A _ M horder (m+1) below.le
  let I₁ := VacuumAuxiliaryInput.atCarrier F₁ P.output.carrier hwell b hb E hE C
    (by
      intro U
      have h := hExp U
      rw [hnil, ← hclip] at h
      rw [hlayers]
      exact h) T x₀ hT P.actual_forced hpackets
  exact ⟨I₁, ⟨P.actual_forced, hreserved, le_rfl, zero_le_one⟩,
    HEq.rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, P.output.output_vacuum R.makes below hfine⟩

end YM.Integration.QuadraticVacuumReentry
