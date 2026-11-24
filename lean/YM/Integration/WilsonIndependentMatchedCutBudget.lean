import YM.Integration.WilsonIndependentMatchedCoverPairBudget

/-! The actual normalized cover school buys its own upper single-source
charges before any pair and before any choices of its seats. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCutBudget
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedSeatedIncome WilsonIndependentMatchedCoveredSeats
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

open WilsonIndependentMatchedCoverPairBudget
def restored (X:CutsP H T p v E W K U)(a δ η:ℝ):ℝ:= |a| * (δ^(-η)*X.fuel)

theorem original (run:XSpace.Run)(B₀ η:ℝ)(small:0<η):
    ∀ᶠ idx:ℕ in atTop,∀(X:CutsP H T p v E W K U)(a:ℝ),let δ:=(run.step idx).spacing
    X.vesselsC.y X.m ≤ B₀ → WilsonOriginalPublicPlantedStableCredit.span X X.i=-Real.log δ →
    Bought X a δ (restored X a δ η):=by
  filter_upwards [WilsonOriginalPublicPlantedStableCredit.original H T p v E W K U run B₀ η small]
    with idx funded X a δ base optical i hi j hj r z hz
  have earned:=(funded X base optical j hj i hi r z hz).μ a
  have space:Real.exp (-WilsonOriginalPublicPlantedStableCredit.span X i)=paceT X.ax.S X.m (X.m+i):=
    WilsonIndependentMatchedCoverSum.spacing X.ax.S X.m i
  rw [space] at earned
  convert earned using 1
  · rfl
  · unfold restored
    ring

end YM.Integration.WilsonIndependentMatchedCutBudget
