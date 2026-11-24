import YM.Integration.WilsonLimitConstruction.FundedChartSelection
import YM.RG01Estimate.Stamped

/-! A prescribed manuscript demand has an actual price on the native company.
Its output controls the complete retention coefficient and shipping register. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedChartDemand

open RG01Estimate.Chart

theorem allPrices {G : Gauge} (hG : G.Simple) (demand : Demand G) :
    FundedPredictionSupply.AllPrices (G:=G)
      (fun {_} {_} {_} R => Stamped demand R) :=
  FundedChartSelection.allPrices (activated demand hG)

end YM.Integration.WilsonLimitConstruction.FundedChartDemand
end
