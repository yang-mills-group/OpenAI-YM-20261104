import YM.Integration.ActualRunRetunedVacuum
import YM.Integration.NonnegativeVacuumLayerRescaling

/-! The actual selected ratio is nonnegative even without a positive
predictor. The separate zero case supplies a genuine graded list without
adding predictor positivity to the current retained Grant. Quantitative
ratio and next-admission bounds remain separate. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunRetunedGraded

open Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Classical

variable {G : Gauge} (run : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities}
    {Y : YM.Comparison.RG02.Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}
    (M : AnalyticOutput caps Y K F)

/-- This uses only the total real square root and the actual Run coupling. -/
theorem ratio_nonnegative : 0 ≤ ActualRunRetunedVacuum.ratio run M := by
  exact div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (Currency.g_pos run.makes datum.cutoff datum.period datum.level datum.below.le).le

/-- No new Plan-positivity premise. All original selected layers and physical
row identities are those of ActualRunRetunedVacuum.retunedLayers. -/
def graded :
    GradedVacuumLayers (ActualRunRetunedVacuum.retunedLayers run M)
      (A.outputNorm datum.level) J.order caps.vacuumRank
      (A.outputWidth datum.level)
      (NonnegativeVacuumLayerRescaling.multiplier
        (ActualRunRetunedVacuum.ratio run M) J.order * K.geometry datum.level) :=
  NonnegativeVacuumLayerRescaling.nonnegative_graded M.vacuum
    (ratio_nonnegative run M)

end YM.Integration.ActualRunRetunedGraded
end
