import YM.Integration.WilsonReportColumnSubsidy
import YM.Integration.WilsonWindowReportingRun
import YM.GapsR2RG.CampaignStencil

/-! The full column reserve and the logarithm for the chosen physical
factory. The original Pillars name its actual Music in every period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCitizenRun

open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowJointPurchase

universe u

theorem on_run {G : Gauge} (hG : G.Simple) {ε : ℝ} {R : Run G}
    {T : Campaign R} (W : Campaign.Pillars R T)
    (original : FundedOriginalProperties.{u} hG ε W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) :
    Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  have book := original.2.1.logBudget
  have funding := original.2.1.paid
  exact ⟨Campaign.citizenTie book.toPackage W hG funding.fixed
    funding.stoves funding.logCopy subsidy, book⟩

theorem select {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (p : Prediction G) (paid : WilsonFundedWindowMenu.AllPrices (@p)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      p R.kit ∧ WilsonWindowTicketPurchase.Issued hG R.kit ∧
      WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨R,T,W,⟨hp,hs⟩,ticket,pace,archive,correlations,original⟩ :=
    WilsonWindowReportingRun.select.{u} hG hε
      (Together (@p) (@WilsonReportColumnSubsidy.Eligible G))
      (fun s price => joint (paid s price) (WilsonReportColumnSubsidy.allPrices s price))
  exact ⟨R,T,W,hp,ticket,pace,archive,correlations,original,on_run hG W original hs⟩

end YM.Integration.WilsonReportCitizenRun
end

