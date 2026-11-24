import YM.Integration.WilsonWindowSchoolInvoice
import YM.Integration.WilsonReportColumnSubsidy
import YM.Integration.WilsonWindowUniversalSchool
import YM.Integration.WilsonPosteriorProjectionPrescribedSchedule
import YM.Integration.WilsonConditionalTaylorTailPurchase
import YM.Integration.WilsonPhysicalExteriorPresoldRun

/-! One original existence witness before the marked school, its canonical
formal trajectory, every finite roster of measured fields and every rooted
conditional comparison. Further prepaid requirements remain admissible. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSelectedMarkedHistory

open Function Filter Finset Lattice Wilson RG RG.Shoot RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open MSbar MSbar.Heath FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open WilsonConditionalTaylorLabels WilsonWindowRootPurchase WilsonWindowJointPurchase
open WilsonWindowBookPurchase WilsonWindowUniversalSchool
open scoped Classical

universe u
variable {G : Gauge} {φ : ℕ → ℕ}

theorem select (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (u : G.ColorIndex)
    (V : Voice G) (cle : Clear G V) (C : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      more R.kit ∧ WilsonConditionalTaylorPurchase.Inventory u V R.kit ∧
      WilsonConditionalTaylorTailPurchase.dues V cle hG R.kit ∧
      (∃ B F, Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p)) ∧
      WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧
      WilsonWindowFormalPurchase.Canonical U R.kit ∧ WilsonConditionalTaylorPosterior.Posterior R u ∧
      (∀ a : Roster G, FluctuationMaskReadings (lamps a) R u) ∧
      (∀ e : WilsonConditionalTaylorLabels.Entry G, WilsonPosteriorProjectionRootedSchedule.AllOrders e R u) ∧
      (∀ e : WilsonConditionalTaylorLabels.Entry G, WilsonPosteriorProjectionPrescribedSchedule.Full e R u) ∧
      NativeFVAPlateau.Correlations R ∧ WilsonPhysicalExteriorPresoldRun.Books hG R ∧
      FundedOriginalProperties.{u} hG ε W ∧
      PhysicalNext.Repeat.Legato.Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  let law := Tracks.vine (flow C) split
  have prepaid := WilsonWindowSchoolInvoice.prepaid hG law U
    (fun s M => WilsonWindowCourseLaws.physical_course split (external s M))
  obtain ⟨R,T,W,⟨outside,caliper,tails,school⟩,posterior,masks,rooted,prescribed,corr,original,citizen,logBook⟩ :=
    WilsonPosteriorProjectionPrescribedSchedule.select.{u} hG hε u V cle
      (Together (@more) (Together (@WilsonConditionalTaylorPurchase.Inventory G u V)
        (Together (@WilsonConditionalTaylorTailPurchase.dues G V cle hG)
          (@WilsonWindowSchoolInvoice.grant G φ hG law U))))
      (fun s M => WilsonWindowJointPurchase.joint (credit s M)
        (WilsonWindowJointPurchase.joint (WilsonConditionalTaylorPurchase.prepaid hG u V cle s _)
          (WilsonWindowJointPurchase.joint (WilsonConditionalTaylorTailPurchase.prepaid V cle hG s (ThroughLaunch.raging s M))
            (prepaid s M))))
  obtain ⟨⟨B,chamber⟩,admit,slow,archive,formal⟩ :=
    WilsonWindowSchoolInvoice.on_run hG R law U school
  obtain ⟨F,school⟩ := house hG R _ _ C B split chamber admit
  have books : WilsonPhysicalExteriorPresoldRun.Books hG R :=
    fun N M dial => WilsonPhysicalExteriorIssuedWord.funded R hG N M dial corr
  exact ⟨R,T,W,outside,caliper,tails,⟨B,F,school⟩,slow,archive,formal,posterior,masks,rooted,prescribed,corr,books,original,citizen,logBook⟩

/-- The original probe course, the independent cost constants and the true
report-column subsidy are all supplied before the physical run. -/
theorem purchased (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (u : G.ColorIndex) (U : ℕ → ℕ) :
    ∃ (V : Voice G) (clear : Clear G V) (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      WilsonReportColumnSubsidy.Eligible R.kit ∧ WilsonConditionalTaylorPurchase.Inventory u V R.kit ∧
      WilsonConditionalTaylorTailPurchase.dues V clear hG R.kit ∧
      (∃ B F, Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        (VowsR.probe G MintClock.splits) B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p)) ∧
      WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧
      WilsonWindowFormalPurchase.Canonical U R.kit ∧ WilsonConditionalTaylorPosterior.Posterior R u ∧
      (∀ a : Roster G, FluctuationMaskReadings (lamps a) R u) ∧
      (∀ e : WilsonConditionalTaylorLabels.Entry G, WilsonPosteriorProjectionRootedSchedule.AllOrders e R u) ∧
      (∀ e : WilsonConditionalTaylorLabels.Entry G, WilsonPosteriorProjectionPrescribedSchedule.Full e R u) ∧
      NativeFVAPlateau.Correlations R ∧ WilsonPhysicalExteriorPresoldRun.Books hG R ∧
      FundedOriginalProperties.{u} hG ε W ∧
      PhysicalNext.Repeat.Legato.Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨V,clear⟩ := MSbar.Heath.vocals G
  refine ⟨V,clear,?_⟩
  refine select.{u} hG hε u V clear (VowsR.probe G MintClock.splits) le_rfl ?_ U
      (@WilsonReportColumnSubsidy.Eligible G) WilsonReportColumnSubsidy.allPrices
  intro s price R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact ⟨V,Push.PriceCompiler.DelayLe.refl _,fun _ _ => trivial⟩

end YM.Integration.WilsonSelectedMarkedHistory


