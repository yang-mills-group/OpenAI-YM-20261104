import YM.Integration.WilsonReportingAbsoluteInletPrior
import YM.Integration.WilsonWindowOriginalHardRadius
import YM.Integration.WilsonWindowSchoolInvoice
import YM.Integration.WilsonWindowUniversalSchool

/-! The original marked school, actual funded existence fields, and the two
absolute inlet estimates on one campaign for every later finite reporting order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool
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
      (∀ j, cap j ≤ (R.metals.p.profile j).order) ∧ more R.kit ∧ StationInvoice R ∧
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
        AllAnchors R Θ.price := by
  let law := Tracks.vine (flow C) split
  let p : Prediction G := @Together G (@Together G (@more) (@WilsonWindowOriginalHardRadius.Booked G))
    (@Together G (@WilsonReportColumnSubsidy.Eligible G) (@WilsonWindowSchoolInvoice.grant G φ hG law U))
  have school := WilsonWindowSchoolInvoice.prepaid hG law U
    (fun s M => WilsonWindowCourseLaws.physical_course split (external s M))
  have paid : WilsonFundedWindowMenu.AllPrices (@p) := fun s M =>
    joint (joint (credit s M) (WilsonWindowOriginalHardRadius.allPrices s M)) (joint (WilsonReportColumnSubsidy.allPrices s M) (school s M))
  obtain ⟨R,T,W,tall,⟨⟨outside,hard⟩,subsidy,booked⟩,station,aperture,correlations,original,_,Θ,v,custody,sky,dates,report,anchors⟩ :=
    WilsonReportingAbsoluteInletPrior.original.{u} cap mono hG hε φ (@p) paid
  obtain ⟨⟨B,chamber⟩,admit,pace,archive,formal⟩ := WilsonWindowSchoolInvoice.on_run hG R law U booked
  obtain ⟨F,house_paid⟩ := house hG R _ _ C B split chamber admit
  obtain ⟨citizen,logBook⟩ := WilsonReportCitizenRun.on_run.{u} hG W original subsidy
  exact ⟨R,T,W,tall,outside,station,hard,⟨B,F,house_paid⟩,aperture,pace,archive,formal,correlations,
    original,citizen,logBook,Θ,v,custody,sky,dates,report,anchors⟩

end YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool
