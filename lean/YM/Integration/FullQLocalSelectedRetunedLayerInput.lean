import YM.Integration.ActualRunInterpolatedInput
import YM.Integration.ActualRunRetunedGraded
import YM.Integration.ActualGradedVacuum
import YM.Integration.ActualRunRetainedPreparation

/-!
The literal rescaled returned list supplies Grade5 colors for the same
finite-copy next packet. The complete selected physical output, quiet
correction, gas and marked residual remain in the full preparation.

The ratio-zero branch uses the genuine nonnegative rescaling receipt.
No predictor positivity or new numerical payment premise is inserted.
The parent's exact multiplier is one at zero and factorBound otherwise;
next norm/cost admission, affine reset and cross-chart jets remain separate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric
open Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02 PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum
open Comparison.RG02.Assembly
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {R0 : Run G} {J : Request V} {A : NumericSchedule R0.family J}
    {datum : LocalFormal.Datum R0.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R0.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}


namespace AnalyticOutput

/-- The exact native rescaled list, at the fixed ratio determined by this M. -/
def retunedLayerVacuum (M : AnalyticOutput caps Y K F) :
    ℝ → Config G (R0.family.side datum.level datum.period) → ℝ :=
  ActualGradedVacuum.restored (ActualRunRetunedVacuum.retunedLayers R0 M)

/-- The same-M nonnegative-ratio graded receipt handles zero as well as
positive ratio. Its numerical multiplier is retained by that parent;
this conclusion supplies only the qualitative vacuum inlet. -/
theorem retuned_layer_receipts (M : AnalyticOutput caps Y K F) :
    GradeAt 5 (Bulk.projected M.retunedLayerVacuum) ∧
      (∀ g : ℝ, GaugeInvariant (M.retunedLayerVacuum g)) ∧
      (∀ g : ℝ, Envelope (M.retunedLayerVacuum g)) := by
  let H := ActualRunRetunedGraded.graded R0 M
  exact ⟨ActualGradedVacuum.restored_grade H (A.output_width_pos datum.level),
    ActualGradedVacuum.restored_gauge H,
    ActualGradedVacuum.restored_envelope H (A.output_width_pos datum.level)⟩

end AnalyticOutput

namespace Retained
variable {eta_w : ℝ} {I : FullPreparedInputAt F eta_w}
    {M : AnalyticOutput caps Y K F}

/-- Fixed from the already selected output capacity, before every row/test. -/
private theorem selected_power_floor (S : Chosen K I M) :
    ∀ i T, S.output.model.packet i = some T →
      0 < ((caps.packetPower + 1 : ℕ) : ℤ) + S.output.model.power i := by
  intro i T hT
  have hcap : S.output.model.powerCap ≤ caps.packetPower := by
    simpa only [S.same_model] using M.power_bounded
  have hp := (S.output.model.power_bounded i T hT).trans hcap
  have ha : |S.output.model.power i| ≤ (caps.packetPower : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hp
  have hl := (abs_le.mp ha).1
  omega

/-- The actual finite-copy next packet and the exact rescaled returned-layer vacuum. -/
def Chosen.onRun_retuned_layer_colors (S : Chosen K I M) (r : ℕ) :
    TestSpace J.tests → Bulk.Colors B G
      (R0.family.side datum.level datum.period) :=
  ActualRunInterpolatedInput.colors R0 datum.cutoff datum.period datum.level
    S.output.model r (caps.packetPower + 1) M.retunedLayerVacuum

/-- No extra vacuum receipt or occupied-row floor is assumed. -/
theorem Chosen.onRun_retuned_layer_input (S : Chosen K I M) (r : ℕ) :
    InputColors (S.onRun_retuned_layer_colors r)
      (ActualRunInterpolatedPackets.onRun R0 datum.cutoff datum.period
        datum.level S.output.model r) := by
  have hPaid := M.paid
  rw [← S.same_model] at hPaid
  obtain ⟨hv, hG, hE⟩ := M.retuned_layer_receipts
  exact ActualRunInterpolatedInput.input_colors R0 datum.cutoff datum.period
    datum.level datum.below S.output.model r (caps.packetPower + 1)
    (selected_power_floor S) hPaid M.retunedLayerVacuum (hv.lower (by decide)) hG hE

/-- These colors have the genuine standard grade five from the exact rescaled
returned layer list, for every independent test tuple. -/
theorem Chosen.onRun_retuned_layer_standard (S : Chosen K I M) (r : ℕ)
    (x : TestSpace J.tests) : (S.onRun_retuned_layer_colors r x).Standard := by
  refine ⟨(S.onRun_retuned_layer_input r).well x, ?_⟩
  change GradeAt 5 (Bulk.projected M.retunedLayerVacuum)
  exact (M.retuned_layer_receipts).1

end Retained
end YM.Integration.FullQLocal.RenderedStep.Numeric

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02 PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}

/-- The full rough output is prepared with the concrete Grade5 rescaled-layer colors and
its original residual. The physical vacuum equality is propagated on the
same carrier, separately from the model-vacuum analytic receipts. -/
theorem Grant.onRun_retuned_layer_full_preparation (R0 : Run G)
    {J : Request V} {A : NumericSchedule R0.family J}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R0.family.path}
    {floor n : ℕ → ℕ} {pre : PreBlockConstant}
    (H : Grant (R := B) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : UniformlyFlat (C := R0.family) J eta_w)
    (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : (H.family eta_w flat).first ≤ later,
      ∀ (datum : LocalFormal.Datum R0.family B) (hm : later ≤ datum.level)
        (hfloors : Handoff.LocalFloors floor n datum)
        (hulls : ShortHulls H.models.prices datum) (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
        (intake : NativeIntake I),
      let S := (H.family eta_w flat).select datum (hlater.trans hm)
        hfloors hulls F I intake
      ∀ (_hFine : I.carrier.rep.eval =
          (R0.family.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
        (r : ℕ),
        S.output.carrier.rep.eval =
          (R0.family.path.rep datum.cutoff datum.period datum.level).eval ∧
        ∃ P : PreparedWithRemainderAt datum.cutoff datum.period datum.level
            (A.outputNorm datum.level) (Handoff.legacyCarrier S.output.carrier)
            F.coarseRoots S.output.output (S.onRun_retuned_layer_colors r)
            (ActualRunInterpolatedPackets.onRun R0 datum.cutoff datum.period
              datum.level S.output.model r)
            F.outputRadii (envelopeProduct F.kernelCosts)
            (ordinaryRate H.models.prices I delta)
            ((Pert.Asymptotics.regulatorRun R0.family datum.cutoff datum.period
              (datum.level + 1)) ^ forcedOrder),
          P.remainder = S.output.residual := by
  obtain ⟨later, hlater, hNext⟩ :=
    Grant.onRun_next_preparation R0 H eta_w flat delta hdelta forcedOrder
  refine ⟨later, hlater, ?_⟩
  intro datum hm hfloors hulls F I intake
  dsimp only
  intro hFine r
  let S := (H.family eta_w flat).select datum (hlater.trans hm)
    hfloors hulls F I intake
  constructor
  · exact S.output.output_vacuum R0.makes datum.below hFine
  · exact hNext datum hm hfloors hulls F I intake r
      (S.onRun_retuned_layer_colors r) (S.onRun_retuned_layer_input r)

end YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
end
