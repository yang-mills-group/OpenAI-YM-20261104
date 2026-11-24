import YM.Integration.PhysicalWilsonSignedOutput
import YM.Integration.WilsonLimitConstruction.FundedRenderedBank

/-! Quantitative projections of the true signed analytic output use its
actual marked model and the same physical graded vacuum layers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSignedCostModels
open Filter Lattice RG RG.Supply Precision Marker
open RG3.Script.Picnic Comparison.RG02 IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalWilsonActionConvention
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A d}

def catalogue (M : SignedAnalyticOutput caps Y K F) : FundedRenderedBank.Catalogue J d :=
  ⟨M.model,M.plan⟩

structure Width (width : ℕ→ℝ) (M : SignedAnalyticOutput caps Y K F) where
  vacuum : GradedVacuumLayers (M.plan.layers d.level) (A.outputNorm d.level)
    J.order caps.vacuumRank (width d.level) (K.geometry d.level)
  paid : M.model.Paid (A.outputNorm d.level) F.outputAddresses M.region
    (fun v => F.outputRadii v/F.kernelCosts v) (Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1))
    (width d.level) (K.geometry d.level) M.coverOffset M.coverSlope

def own_width (M : SignedAnalyticOutput caps Y K F) : Width A.outputWidth M :=
  ⟨M.vacuum,M.paid⟩

end YM.Integration.WilsonLimitConstruction.FundedSignedCostModels
end
