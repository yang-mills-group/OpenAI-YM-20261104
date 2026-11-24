import YM.LocalTaylorR2.Strange.Bayes
import YM.Integration.WilsonMovingRoutedRegister

/-! The four original calendar expenses consumed by the bent Wilson regular-action estimate, timed before the common block and delay. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorBentWallet
open LocalTaylorR2
open Exponent
open King (overD capping SupplyF)
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
open Reel Recoil Capstone Strand Rain Roost Mallow PhysicalNext.Repeat.Legato UVExtension Spire Orchard Mast Oasis LocalTaylorR2.Marker
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonMovingRoutedRegister (Earned)
variable {G : Gauge}

def Paid : Prediction G := fun {_} {_} {A} F =>
  Mallow.RG12.Earned (ticketD G) F.shape A.delay ∧
  Mallow.RG12.Earned (wheelD G) F.shape A.delay ∧
  Mallow.RG12.Earned (Exponent.reckon (Strange.jetEngine G).toObservatory) F.shape A.delay ∧
  Mallow.RG12.Earned (King.overD G) F.shape A.delay

theorem prepaid : FundedPredictionSupply.AllPrices (@Paid G) := by
  intro s t
  exact FundedPredictionSupply.both (WilsonMovingRoutedRegister.prepaid (ticketD G) s t)
    (FundedPredictionSupply.both (WilsonMovingRoutedRegister.prepaid (wheelD G) s t)
      (FundedPredictionSupply.both
        (WilsonMovingRoutedRegister.prepaid (Exponent.reckon (Strange.jetEngine G).toObservatory) s t)
        (WilsonMovingRoutedRegister.prepaid (King.overD G) s t)))

end YM.Integration.WilsonMovingMentorBentWallet
end
