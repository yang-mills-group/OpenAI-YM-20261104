import YM.Integration.FullQLocalRetainedGrant

/-!
Direct use of the single fixed-domain full-q grant. The bound used for the
next full preparation is obtained from the same selected output in that
grant. There is no additional majorant assumption. The actual retuned read
and analytic color convention are construction inputs, and this conclusion
does not by itself assemble a next AnalyticInput or establish its native
component/order admission.
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
    {R : Census V} {C : Family G} {J : Request V}
    {A : NumericSchedule C J} {caps : Handoff.OutputCapacities}
    {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ} {pre : PreBlockConstant}

/-- One shared tail yields the next full preparation on every actual selected
output, after the same packet's all-test physical read has been proved. -/
theorem Grant.next_preparation (H : Grant (R := R) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : UniformlyFlat (C := C) J eta_w)
    (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : (H.family eta_w flat).first ≤ later,
      ∀ (datum : LocalFormal.Datum C R) (hm : later ≤ datum.level)
        (hfloors : Handoff.LocalFloors floor n datum)
        (hulls : ShortHulls H.models.prices datum) (F : AnalyticInput J A datum)
        (I : FullPreparedInputAt F (eta_w datum.cutoff datum.period datum.level))
        (intake : NativeIntake I),
      let S := (H.family eta_w flat).select datum (hlater.trans hm)
        hfloors hulls F I intake
      ∀ (colors : TestSpace J.tests → Bulk.Colors R G
          (C.side datum.level datum.period))
        (packets : MarkedPackets J.tests G (C.side datum.level datum.period) R)
        (_hColors : InputColors colors packets)
        (_hRead : ∀ x U,
          packets.read x (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
            datum.level) U =
          S.output.model.read x (Pert.Asymptotics.regulatorRun C datum.cutoff
            datum.period (datum.level + 1)) U),
      ∃ P : PreparedWithRemainderAt datum.cutoff datum.period datum.level
          (A.outputNorm datum.level) (Handoff.legacyCarrier S.output.carrier)
          F.coarseRoots S.output.output colors packets F.outputRadii
          (envelopeProduct F.kernelCosts) (ordinaryRate H.models.prices I delta)
          ((Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
            (datum.level + 1)) ^ forcedOrder),
        P.remainder = S.output.residual := by
  obtain ⟨later, hlater, hbound⟩ :=
    H.eventually_bounds eta_w flat delta hdelta forcedOrder
  refine ⟨later, hlater, ?_⟩
  intro datum hm hfloors hulls F I intake
  dsimp only
  intro colors packets hColors hRead
  let S := (H.family eta_w flat).select datum (hlater.trans hm)
    hfloors hulls F I intake
  obtain ⟨bound⟩ := hbound datum hm hfloors hulls F I intake
  exact ⟨S.prepareNext bound colors packets hColors hRead, rfl⟩

end YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
end
