import YM.Integration.LocalComparisonUniformModelPrice
import YM.Integration.FullQLocalRetainedGrant

/-! The same selected model inherits its actual paid all-field multiplier
invoice. The rank cap is the one selected before the block choice; all
marker modes, coupling powers and nonlinear completion terms remain. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
open Lattice Wilson RG Marker
open LocalComparison LocalComparison.Global
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}

theorem Chosen.uniform_model_price (S : Chosen K I M)
    (x : IndependentTests J.tests) (U : Config G (C.side datum.level datum.period)) :
    Poly.price (fun v => F.outputRadii v / F.kernelCosts v)
      (S.output.modelValue (testInclusion J.tests x) U) ≤
      MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V)
        (K.geometry datum.level) := by
  have h := M.paid.uniform_model caps.packetRank M.rank_bounded x U
  simpa only [ProducedOutput.modelValue, S.same_model] using h

end YM.Integration.FullQLocal.RenderedStep.Numeric.Retained
end
