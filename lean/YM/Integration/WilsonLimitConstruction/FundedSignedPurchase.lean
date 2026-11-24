import YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue
import YM.Integration.WilsonLimitConstruction.FundedSignedCatalogue

/-! Project the numerical purchase of an exact signed finite model. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue
open Lattice Wilson RG Marker Comparison.RG02
open PhysicalWilsonActionConvention LocalComparison
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain C.path} {K : NumericPrices A} {F : AnalyticInput J A d}

def ofSigned (M : SignedAnalyticOutput caps Y K F) : Purchase caps K F :=
  ⟨FundedSignedCostModels.catalogue M,M.rank_bounded,M.power_bounded,M.fine_layers,M.output_layers_paid,
    M.vacuum,M.region,M.coverOffset,M.coverSlope,M.cover_cost,M.paid⟩

def widthOfSigned (M : SignedAnalyticOutput caps Y K F) {width : ℕ→ℝ} (H : FundedSignedCostModels.Width width M) :
    Width width (ofSigned M) := ⟨H.vacuum,H.paid⟩

end YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue
end
