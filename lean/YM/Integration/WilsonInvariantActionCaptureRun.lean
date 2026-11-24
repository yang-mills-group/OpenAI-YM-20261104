import YM.Integration.WilsonOriginalIncidentForest
import YM.Integration.WilsonReportColumnSubsidy
import YM.GapsR2RG.CampaignStencil

/-! Buy the genuine all-columns capture on the original marked physical run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCaptureRun
open Function Filter Set MeasureTheory Lattice Wilson RG Precision RG.Supply Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Rank
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowJointPurchase
universe u v

theorem on_run {G:Gauge} (hG:G.Simple) {ε:ℝ} {R:Run G} {T:Campaign R}
    (W:Campaign.Pillars R T) (original:FundedOriginalProperties.{u} hG ε W)
    (subsidy:WilsonReportColumnSubsidy.Eligible R.kit):
    Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors:=by
  have book:=original.2.1.logBudget
  have funding:=original.2.1.paid
  exact Campaign.citizenTie book.toPackage W hG funding.fixed funding.stoves funding.logCopy subsidy

theorem selected {G:Gauge} (hG:G.Simple) {ε:ℝ} (hε:0<ε)
    (prediction:Prediction G) (paid:WilsonFundedWindowMenu.AllPrices (@prediction)):
    ∃ (R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
      prediction R.kit ∧ WilsonWindowReportingPace.Slow R.kit ∧ WilsonOriginalMarkedMenu.Marked.{v} R ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      WilsonOriginalIncidentForest.ForestEstimate R:=by
  let both:Prediction G:=fun {_} {_} {_} k=>prediction k ∧ WilsonReportColumnSubsidy.Eligible k
  obtain ⟨R,T,W,requested,slow,marked,correlations,funded,forest⟩:=
    WilsonOriginalIncidentForest.selectedWith.{u,v} hG hε (@both)
      (fun s t=>WilsonWindowJointPurchase.joint (paid s t) (WilsonReportColumnSubsidy.allPrices s t))
  exact ⟨R,T,W,requested.1,slow,marked,correlations,funded,on_run hG W funded requested.2,forest⟩

end YM.Integration.WilsonInvariantActionCaptureRun
