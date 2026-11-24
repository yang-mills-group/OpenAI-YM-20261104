import YM.Integration.FullQLocalRetainedApplication
import YM.Integration.ActualRunInterpolatedPackets

/-!
Apply the retained full-q grant with the literal corrected packet on one
original Run. The selected model's own Paid field supplies the exact
all-test physical read theorem; no read-equality premise is added.

The new vacuum and InputColors still need their genuine construction.
The resulting full preparation is paid at the returned output norm, and
does not assert the remaining next-input admission or price recurrence.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02 PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}

/-- The same-Run corrected packet removes the generic read-equality inlet.
The whole selected residual remains the next ordinary/forced state. -/
theorem Grant.onRun_next_preparation (R0 : Run G)
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
      ∀ (r : ℕ) (colors : TestSpace J.tests → Bulk.Colors B G
          (R0.family.side datum.level datum.period)),
      let packets := ActualRunInterpolatedPackets.onRun R0 datum.cutoff
        datum.period datum.level S.output.model r
      ∀ _hColors : InputColors colors packets,
      ∃ P : PreparedWithRemainderAt datum.cutoff datum.period datum.level
          (A.outputNorm datum.level) (Handoff.legacyCarrier S.output.carrier)
          F.coarseRoots S.output.output colors packets F.outputRadii
          (envelopeProduct F.kernelCosts) (ordinaryRate H.models.prices I delta)
          ((Pert.Asymptotics.regulatorRun R0.family datum.cutoff datum.period
            (datum.level + 1)) ^ forcedOrder),
        P.remainder = S.output.residual := by
  obtain ⟨later, hlater, hNext⟩ :=
    H.next_preparation eta_w flat delta hdelta forcedOrder
  refine ⟨later, hlater, ?_⟩
  intro datum hm hfloors hulls F I intake S r colors packets hColors
  let M := H.models.realize datum
    ((H.family eta_w flat).after_model.trans (hlater.trans hm)) hfloors hulls F
  have hPaid := M.paid
  have hmodel : S.output.model = M.model := S.same_model
  rw [← hmodel] at hPaid
  exact hNext datum hm hfloors hulls F I intake colors packets hColors
    (fun x U => ActualRunInterpolatedPackets.onRun_read R0 datum.cutoff
      datum.period datum.level datum.below S.output.model r hPaid x U)

end YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
end
