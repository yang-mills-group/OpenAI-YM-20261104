import YM.Integration.WilsonReceivedCloseElectedProgram
import YM.Integration.WilsonReceivedCloseSchoolElection

/-! The original funded existence run carries the signed, independently prescribed near-top three-field comparison at every requested finite order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseFundedThermometer
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonWindowBookPurchase WilsonWindowUniversalSchool
open WilsonReportingAbsoluteInletSimultaneous
open scoped Classical
open FVA1 Extraction Table Climb
universe u
variable {G : Gauge} {φ : ℕ → ℕ}

theorem original (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :

    ∃ (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),
      (∀j,cap j≤(R.metals.p.profile j).order) ∧ more R.kit ∧ StationInvoice R ∧
      WilsonWindowOriginalHardRadius.Booked R.kit ∧ WilsonWindowReportingPace.Slow R.kit ∧
      WilsonWindowOriginalRun.ArchivedInputs R.kit ∧ WilsonWindowFormalPurchase.Canonical U R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      (∃ Θ v, (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧
        Campaign.Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.PanelDates R ∧
        WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧ AllAnchors R Θ.price) ∧
      ∃ books ahead, Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        C books R.family.path.levels.clock.kernel.penalty ahead (stages R.metals.p) ∧
        ∀ (f:Extraction.Order) (F:(Bel R.family.book).Hierarchy) (q span sh:ℕ) (H angleCap cap' tol:ℝ),
          0 ≤ angleCap → 0 ≤ cap' → 0 < tol →
          WilsonReceivedCloseElectedProgram.Heard R hG (roots hG R.metals.p R.metals.K)
            (rollTab hG R.metals R.rolls) books ahead (f:=f) (F:=F) q span sh H angleCap cap' tol := by
  obtain ⟨R,T,W,tall,extra,salary,station,hard,⟨books,ahead,house⟩,protect,slow,archive,formal,correlations,
    fund,citizen,logBook,sky⟩:=WilsonReceivedCloseSchoolElection.original.{u} cap mono hG hε C split external U
      (@more) credit
  refine ⟨R,T,W,tall,extra,station,hard,slow,archive,formal,correlations,fund,citizen,logBook,sky,books,ahead,house,?_⟩
  intro f F q span sh H angleCap maxSpan tol hp cp ep
  exact WilsonReceivedCloseElectedProgram.original R hG (roots hG R.metals.p R.metals.K)
    (rollTab hG R.metals R.rolls) C books ahead house (f:=f) (F:=F) fund slow protect salary.1 salary.2
    q span sh H angleCap maxSpan tol hp cp ep

end YM.Integration.WilsonReceivedCloseFundedThermometer
end
