import YM.Integration.WilsonPhysicalMarkedDefectSingletonRent
import YM.Integration.WilsonSelectedMarkedHistory

/- The one physical selection keeps the complete marked history, the original
report subsidy and both the caller's law and the exact registration radius.
Every declaration concerns the same roots, tab, books, delay and run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.SingletonRent
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
variable {G:Gauge} {φ:ℕ→ℕ} {ε:ℝ}

structure Selection (simple:G.Simple) (u:G.ColorIndex) (U:ℕ→ℕ) (C:VowsR.LawScroll G φ)
    (extra:Prediction G) (V:Voice G) (clear:Clear G V)
    (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T) (accuracy:ℝ) : Prop where
  requested : extra R.kit
  report : WilsonReportColumnSubsidy.Eligible R.kit
  inventory : WilsonConditionalTaylorPurchase.Inventory u V R.kit
  tails : WilsonConditionalTaylorTailPurchase.dues V clear simple R.kit
  housed : ∃ B F, Treehouse.VariableHouse R (roots simple R.metals.p R.metals.K)
    (rollTab simple R.metals R.rolls) C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p)
  rent : Paid R.rolls (roots simple R.metals.p R.metals.K) φ R.alloy.delay
  radius : ∀ η:ℝ, 0<η → ∀ᶠ b:ℕ in atTop, ∀ k d,
    k≤R.alloy.B.a.clock.J b → d≤R.alloy.B.a.clock.J b → ∀ a:CoverLabel G d,
      (SingletonRent.radius (Poetry.Agenda.seed (roots simple R.metals.p R.metals.K) φ (Burn.horizon k)
        (R.alloy.B.a.clock.J b)) a)⁻¹ ≤ R.alloy.B.a.clock.hatBeta b^η
  pace : WilsonWindowReportingPace.Slow R.kit
  archive : WilsonWindowOriginalRun.ArchivedInputs R.kit
  canonical : WilsonWindowFormalPurchase.Canonical U R.kit
  posterior : WilsonConditionalTaylorPosterior.Posterior R u
  masks (a:Roster G) : FluctuationMaskReadings (lamps a) R u
  rooted (e:WilsonConditionalTaylorLabels.Entry G) : WilsonPosteriorProjectionRootedSchedule.AllOrders e R u
  prescribed (e:WilsonConditionalTaylorLabels.Entry G) : WilsonPosteriorProjectionPrescribedSchedule.Full e R u
  correlations : NativeFVAPlateau.Correlations R
  books : WilsonPhysicalExteriorPresoldRun.Books simple R
  funded : FundedOriginalProperties.{u} simple accuracy W
  citizen : PhysicalNext.Repeat.Legato.Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors
  logs : OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors

theorem selected (simple:G.Simple) (hε:0<ε) (u:G.ColorIndex) (U:ℕ→ℕ)
    (C:VowsR.LawScroll G φ) (split:MintClock.splits≤φ)
    (external:∀ (s:Sheet G) (M:MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (extra:Prediction G) (credit:WilsonFundedWindowMenu.AllPrices (@extra)) :
    ∃ (V:Voice G) (clear:Clear G V) (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),
      Selection.{u} simple u U C (@extra) V clear R T W ε := by
  obtain ⟨V,clear⟩ := MSbar.Heath.vocals G
  let combined := MintClock.both G φ C (law G φ)
  have both (s:Sheet G) (M:MapPrices) : Permitted combined s (ThroughLaunch.raging s M) :=
    WilsonWindowVacuumLaws.both (external s M) (permitted φ s _)
  obtain ⟨R,T,W,⟨request,subsidy⟩,inv,tails,⟨B,F,school⟩,pace,archive,canonical,
    posterior,masks,rooted,prescribed,corr,books,original,citizen,logs⟩ :=
    WilsonSelectedMarkedHistory.select.{u} simple hε u V clear combined split both U
      (Together (@extra) (@WilsonReportColumnSubsidy.Eligible G))
      (fun s M => WilsonWindowJointPurchase.joint (credit s M) (WilsonReportColumnSubsidy.allPrices s M))
  have elected : Paid R.rolls (roots simple R.metals.p R.metals.K) φ R.alloy.delay :=
    school.licence.employed.obligation.2
  have held : VowsR.Chamber C R.kit (roots simple R.metals.p R.metals.K) (rollTab simple R.metals R.rolls) B :=
    { school.licence.employed with obligation := school.licence.employed.obligation.1 }
  have house : Treehouse.VariableHouse R (roots simple R.metals.p R.metals.K) (rollTab simple R.metals R.rolls)
      C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p) :=
    { school with licence := { school.licence with employed := held } }
  exact ⟨V,clear,R,T,W,request,subsidy,inv,tails,⟨B,F,house⟩,elected,
    subpower φ R simple _ elected,pace,archive,canonical,posterior,masks,rooted,prescribed,corr,books,
    original,citizen,logs⟩

/-- The concrete original probing law, with no hypothesis that a previously
independently chosen run possessed the newly charged external radius. -/
theorem purchased (simple:G.Simple) (hε:0<ε) (u:G.ColorIndex) (U:ℕ→ℕ) :
    ∃ (V:Voice G) (clear:Clear G V) (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),
      Selection.{u} simple u U (VowsR.probe G MintClock.splits) (@WilsonReportColumnSubsidy.Eligible G)
        V clear R T W ε := by
  apply selected.{u} simple hε u U _ le_rfl _ _ WilsonReportColumnSubsidy.allPrices
  intro s price R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact ⟨V,Push.PriceCompiler.DelayLe.refl _,fun _ _ => trivial⟩

end YM.Integration.WilsonPhysicalMarkedDefect.SingletonRent
