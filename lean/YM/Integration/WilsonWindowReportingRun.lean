import YM.Integration.WilsonWindowOriginalRun
import YM.Integration.WilsonWindowJointPurchase
import YM.Integration.WilsonWindowTicketPurchase
import YM.Integration.WilsonWindowReportingPace

/-! Choose the continuum once with the slow physical report window, the
actual kinetic archive, and the universal school ticket. The remaining
prepaid condition is where the marked chamber is bought on that same run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowReportingRun

open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowJointPurchase

universe u

theorem select {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (p : Prediction G) (paid : WilsonFundedWindowMenu.AllPrices (@p)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      p R.kit ∧ WilsonWindowTicketPurchase.Issued hG R.kit ∧
        WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧
        NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨R,T,W,⟨result,ticket,pace,archive⟩,corr,original⟩ :=
    WilsonWindowOriginalRun.select.{u} hG hε
      (Together (@p) (Together (@WilsonWindowTicketPurchase.Issued G hG)
        (Together (@WilsonWindowReportingPace.Slow G) (@WilsonWindowOriginalRun.ArchivedInputs G))))
      (fun s price => joint (paid s price) (joint (WilsonWindowTicketPurchase.prepaid hG s _)
        (joint (WilsonWindowReportingPace.prepaid hG s _) (WilsonWindowOriginalRun.archive_paid s _))))
  exact ⟨R,T,W,result,ticket,pace,archive,corr,original⟩

end YM.Integration.WilsonWindowReportingRun
end

