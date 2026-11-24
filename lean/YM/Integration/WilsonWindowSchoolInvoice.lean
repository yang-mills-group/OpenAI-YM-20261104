import YM.Integration.WilsonWindowMarkedChamber
import YM.Integration.WilsonWindowCourseLaws
import YM.Integration.WilsonWindowFormalPurchase

/-! The marked chamber, measured reporting window and canonical formal
trajectory as one invoice for a *given* physical selector. This allows the
countable Haar-field selector to fund the school on its very same run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowSchoolInvoice

open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase
open WilsonFundedWindowMenu

variable {G : Gauge} {φ : ℕ → ℕ}

def grant (hG : G.Simple) (C : VowsR.LawScroll G φ) (U : ℕ → ℕ) : Prediction G :=
  Together (@WilsonWindowBookPurchase.Held G φ hG C)
    (Together (@WilsonWindowVacuumAdmission.Ready G)
      (Together (@WilsonWindowTicketPurchase.Issued G hG)
        (Together (@WilsonWindowReportingPace.Slow G)
          (Together (@WilsonWindowOriginalRun.ArchivedInputs G) (@WilsonWindowFormalPurchase.Canonical G U)))))

theorem prepaid (hG : G.Simple) (C : VowsR.LawScroll G φ) (U : ℕ → ℕ)
    (price : ∀ (s : Sheet G) (M : MapPrices), WilsonWindowBookPurchase.Permitted C s (ThroughLaunch.raging s M)) :
    AllPrices (@grant G φ hG C U) := fun s M =>
  joint (from_guard (WilsonWindowBookPurchase.prepaid hG C s _ (price s M)))
    (joint (WilsonWindowVacuumAdmission.prepaid hG s _)
      (joint (WilsonWindowTicketPurchase.prepaid hG s _)
        (joint (WilsonWindowReportingPace.prepaid hG s _)
          (joint (WilsonWindowOriginalRun.archive_paid s _) (WilsonWindowFormalPurchase.prepaid U s _)))))

theorem on_run (hG : G.Simple) (R : Run G) (C : VowsR.LawScroll G φ) (U : ℕ → ℕ)
    (purchased : grant hG C U R.kit) :
    (∃ B, VowsR.Chamber C R.kit (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) B) ∧
      WilsonWindowVacuumAdmission.Ready R.kit ∧ WilsonWindowReportingPace.Slow R.kit ∧
      WilsonWindowOriginalRun.ArchivedInputs R.kit ∧ WilsonWindowFormalPurchase.Canonical U R.kit := by
  obtain ⟨held,vac,ticket,slow,archive,formal⟩ := purchased
  exact ⟨WilsonWindowBookPurchase.chamber hG C R.kit held ticket,vac,slow,archive,formal⟩

end YM.Integration.WilsonWindowSchoolInvoice

