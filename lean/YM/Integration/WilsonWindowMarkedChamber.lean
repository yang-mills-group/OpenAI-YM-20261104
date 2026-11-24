import YM.Integration.WilsonReportCitizenRun
import YM.Integration.WilsonWindowBookPurchase
import YM.Integration.WilsonWindowVacuumAdmission

/-! Build the original chamber from ticket and book purchases on a single
funded continuum run. The roots and tab are the preappointed physical ones. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowMarkedChamber

open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase

universe u

theorem selected {G : Gauge} {ψ : ℕ → ℕ} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (law : VowsR.LawScroll G ψ)
    (invoice : ∀ (s : Sheet G) (price : MapPrices),
      WilsonWindowBookPurchase.Permitted law s (ThroughLaunch.raging s price)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (∃ B, VowsR.Chamber law R.kit (roots hG R.metals.p R.metals.K)
        (rollTab hG R.metals R.rolls) B) ∧ WilsonWindowVacuumAdmission.Ready R.kit ∧
        WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧
        NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
        Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
        OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨R,T,W,⟨books,admission⟩,ticket,pace,archive,corr,original,citizen,logBook⟩ :=
    WilsonReportCitizenRun.select.{u} hG hε
      (Together (@WilsonWindowBookPurchase.Held G ψ hG law) (@WilsonWindowVacuumAdmission.Ready G))
      (fun s price => joint
        (WilsonFundedWindowMenu.from_guard (WilsonWindowBookPurchase.prepaid hG law s _ (invoice s price)))
        (WilsonWindowVacuumAdmission.prepaid hG s _))
  exact ⟨R,T,W,WilsonWindowBookPurchase.chamber hG law R.kit books ticket,admission,pace,archive,corr,
    original,citizen,logBook⟩

end YM.Integration.WilsonWindowMarkedChamber
end

