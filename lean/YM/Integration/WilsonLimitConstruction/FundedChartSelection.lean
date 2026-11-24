import YM.Integration.WilsonLimitConstruction.FundedRetargetAgreement
import YM.Integration.WilsonLimitConstruction.FundedPredictionSupply
import YM.RG01Estimate.Plan

/-! Connect the manuscript chart purchase to the preselection point of the
original native company. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedChartSelection

open RG RG.Supply Precision PhysicalNext
open RG01Estimate.Chart

/-- Every funded manuscript prediction can be bought on the same native
sheet and quote before the length and delay selections. -/
theorem prepaid {G : Gauge} {goal : Goal G} (paid : Funds goal)
    (s : Sheet G) (T : MapPrices) :
    FundedCompanySelection.Prepaid (@goal.predicts) s (ThroughLaunch.raging s T) := by
  rw [FundedRetargetAgreement.prices]
  exact paid s T

/-- A manuscript grant supplies the unchanged preselection interface used by
the original native company and the outer treasury construction. -/
theorem allPrices {G : Gauge} {goal : Goal G} (paid : Funds goal) :
    FundedPredictionSupply.AllPrices (@goal.predicts) := fun s T => prepaid paid s T

end YM.Integration.WilsonLimitConstruction.FundedChartSelection
end
