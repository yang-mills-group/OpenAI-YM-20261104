import YM.Integration.WilsonMovingRoutedMayerStage
import YM.Integration.WilsonLimitConstruction.FundedPredictionSupply
import YM.RG12.Burst.Cotton

/-! The ordinary physical register and the separate marked booking each
pay their actual covariance. Their original orders are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingRoutedRegister
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical
open RGLocalTaylor RGLocalTaylor.Laminate
open WilsonLimitConstruction WilsonLimitConstruction.FundedPredictionSupply WilsonGaussianDeterminantTender
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction.FundedCompanySelection
open WilsonOriginalMarkedExistence GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared

variable {G : Gauge}

def Earned (δ : Charity.RG12.Decal G) : Prediction G :=
  fun {_} {_} {A} F => Mallow.RG12.Earned δ F.shape A.delay

theorem prepaid (δ : Charity.RG12.Decal G) : AllPrices (@Earned G δ) := by
  intro s prices targets costs table programs wages baton wants
  obtain ⟨n,firsts⟩ := Mallow.RG12.lint δ targets costs
  refine ⟨n,?_⟩
  intro l enough D w u Z post scouts θ requests prospective V _
  have first : Mallow.RG12.First δ (ThroughLaunch.raise s l) _ _ _ n := firsts
  obtain ⟨W,more,ready⟩ := Mallow.RG12.board δ Z first
    (fun j => (enough j).trans (D.large j).need) (fun j i _ => (wants j i).le) V
  refine ⟨W,more,?_⟩
  intro Y later bar wait tariff funded _alloy η q E X J K b sheltered working divides
  exact ready Y later

theorem physical (R : Run G) (ordinary : Earned (WilsonCoherentMayerCovarianceCalendar.decal G) R.kit)
    (m : ℕ) :
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    WilsonCoherentMayerCovarianceCalendar.deviation G (R.rolls.L j) (R.kit.shape.o j i) ≤
      1 + Real.log (R.alloy.B.a.clock.hatBeta (m+1)) := by
  let j := R.alloy.B.a.clock.J (m+1)
  let i := R.alloy.B.a.clock.J m
  let x := R.alloy.B.a.clock.hatBeta m
  have h := ordinary j x (R.alloy.B.valid.pays m) i (step_paid R.alloy.B.a m)
  change WilsonCoherentMayerCovarianceCalendar.deviation G (R.rolls.L j) (R.kit.shape.o j i) ≤
    1 + Real.log (betaF G x (R.rolls.L j)) at h
  simpa only [j,x,← beta_eq R.alloy.B.valid m] using h

end YM.Integration.WilsonMovingRoutedRegister
end
