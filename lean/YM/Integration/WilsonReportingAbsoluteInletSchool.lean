import YM.Integration.WilsonReportingAbsoluteInletSubmittedForests
import YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool
import YM.Integration.WilsonReportingAbsoluteInletColorMenu

/-! The marked school and every color's independently priced inlet forecast
open on the original funded physical run chosen before the finite accuracy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletSchool

open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open MSbar.Heath WilsonWindowRootPurchase WilsonWindowJointPurchase
open WilsonWindowBookPurchase WilsonWindowUniversalSchool
open WilsonReportingAbsoluteInletForecastMarket WilsonReportingAbsoluteInletForecastElection
open Pert.Asymptotics FormalBulk08 FormalBulk08.Flat FormalBulk08.Series FormalBulk08.Wine
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorLabels WilsonConditionalTaylorCourseAttachment WilsonReportingAbsoluteInletForecastBooks
open WilsonReportingAbsoluteInletSimultaneous
open scoped BigOperators Classical

universe u
variable {G : Gauge} {φ : ℕ → ℕ}

/-- The material books, physical hierarchy and both thermal estimates on one campaign. -/
def OnRun (cap : ℕ → ℕ) (hG : G.Simple) (ε : ℝ) (C : VowsR.LawScroll G φ)
    (U : ℕ → ℕ) (more : Prediction G) (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T) : Prop :=
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
    ∀ a : G.ColorIndex, Bought R a Θ.price ∧ BoughtAnchor R a Θ.price

theorem selected (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (V : Voice G) (clear : Clear G V) (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      OnRun.{u} cap hG ε C U (@more) R T W := by
  classical
  let us := (Finset.univ : Finset G.ColorIndex).toList
  let offers : G.ColorIndex → Prediction G := fun a => @Terms G a V
  have sold (a : G.ColorIndex) : WilsonFundedWindowMenu.AllPrices (@offers a) :=
    fun s M => WilsonReportingAbsoluteInletForecastMarket.prepaid hG a V clear s (ThroughLaunch.raging s M)
  obtain ⟨R,T,W,tall,bill,station,hard,house,aperture,pace,archive,formal,correlations,original,
    citizen,logBook,Θ,v,custody,sky,dates,report,anchors⟩ :=
    WilsonReportingAbsoluteInletPhysicalSchool.original.{u} cap mono hG hε C split external U
      (@WilsonReportingAbsoluteInletColorMenu.colors G (@more) (@offers) us)
      (WilsonReportingAbsoluteInletColorMenu.prices (@more) (@offers) credit sold us)
  obtain ⟨outside,remaining⟩ := WilsonReportingAbsoluteInletColorMenu.reads R (@more) (@offers) us bill
  refine ⟨R,T,W,tall,outside,station,hard,house,aperture,pace,archive,formal,correlations,
    original,citizen,logBook,Θ,v,custody,sky,dates,report,?_⟩
  intro a
  have money : Terms a V R.kit := remaining a (by simp [us])
  exact ⟨on_run R hG a V money report, anchored R hG a V money anchors⟩

/-- The original chamber, active subsidy and physical and formal receipts need
only the ordinary simple Wilson group and positive penalty. -/
theorem original (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (U : ℕ → ℕ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      OnRun.{u} cap hG ε (VowsR.probe G MintClock.splits) U (@WilsonReportColumnSubsidy.Eligible G) R T W := by
  obtain ⟨V,clear⟩ := MSbar.Heath.vocals G
  exact selected.{u} cap mono hG hε V clear (VowsR.probe G MintClock.splits) le_rfl
    (fun _ _ _ _ _ _ => ⟨0,fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ D =>
      ⟨D,Push.PriceCompiler.DelayLe.refl _,fun _ _ => trivial⟩⟩)
    U (@WilsonReportColumnSubsidy.Eligible G) WilsonReportColumnSubsidy.allPrices

end YM.Integration.WilsonReportingAbsoluteInletSchool
end


