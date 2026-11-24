import YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool
import YM.Integration.WilsonReceivedCloseOriginalTuition

/-! Elect the original marked school, the funded existence data and the finite incidence prices on the same roots once, before all requested accuracies. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseSchoolElection
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonWindowBookPurchase WilsonWindowUniversalSchool
open WilsonReportingAbsoluteInletSimultaneous
open scoped Classical
universe u
variable {G : Gauge} {φ : ℕ → ℕ}

theorem original (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (∀ j, cap j ≤ (R.metals.p.profile j).order) ∧ more R.kit ∧ WilsonReceivedCloseOriginalTuition.Funds hG φ R.kit ∧ StationInvoice R ∧
      WilsonWindowOriginalHardRadius.Booked R.kit ∧
      (∃ B F, Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p)) ∧
      WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots hG R.metals.p R.metals.K) φ R.alloy.delay ∧
      WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧
      WilsonWindowFormalPurchase.Canonical U R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} hG ε W ∧
      Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      ∃ Θ v, (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧
        Campaign.Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.PanelDates R ∧
        WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧
        AllAnchors R Θ.price
    := by
  let tuition := @WilsonReceivedCloseOriginalTuition.Funds G hG φ
  have enrolled : WilsonFundedWindowMenu.AllPrices (@Together G (@more) tuition) :=
    fun s M => joint (credit s M) (WilsonReceivedCloseOriginalTuition.prepaid hG φ split s M)
  obtain ⟨R,T,W,tall,⟨entered,source⟩,receipts⟩ :=
    WilsonReportingAbsoluteInletPhysicalSchool.original.{u} cap mono hG hε C split external U
      (@Together G (@more) tuition) enrolled
  exact ⟨R,T,W,tall,entered,source,receipts⟩

end YM.Integration.WilsonReceivedCloseSchoolElection
end
