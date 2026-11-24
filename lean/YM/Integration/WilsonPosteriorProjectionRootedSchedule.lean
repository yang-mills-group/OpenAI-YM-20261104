import YM.Integration.WilsonConditionalTaylorPhysical
import YM.Integration.WilsonPosteriorProjectionRootedAdmissions
import YM.Integration.WilsonPosteriorProjectionRootedCharge
import YM.Integration.WilsonPosteriorProjectionThermalWindow
import YM.Integration.FVA1Physical.Round2.RootedFieldTrajectory

/-! All originally named rooted field comparisons on a *single* funded
existence construction. The true field and independent emitted polynomial
have the same original labels, translations, background and torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionRootedSchedule

open Function Filter Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection Next.Foundations
open MSbar MSbar.Heath FVA1Physical.Wilson FVA1Physical.Round2.Curvature FVA1Physical.Marked
open WilsonConditionalTaylorLabels WilsonConditionalTaylorThreshold WilsonConditionalTaylorCalendar
open WilsonConditionalTaylorFieldPurchase WilsonConditionalTaylorFields WilsonWindowJointPurchase
open WilsonConditionalTaylorPhysical WilsonPosteriorProjectionPinned WilsonPosteriorProjectionRootedRoster
open RGComparison.Core16.Spool
open scoped Classical Topology BigOperators

universe u
variable {G : Gauge}

/-- The quantifiers over every rooted census and its mixed orders are *inside*
the single existential paying the original continuum construction. -/
theorem presold (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (u : G.ColorIndex)
    (V : Voice G) (cle : Clear G V) (more : Prediction G)
    (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      more R.kit ∧ WilsonConditionalTaylorPosterior.Posterior R u ∧
      (∀ a : Roster G, FluctuationMaskReadings (lamps a) R u) ∧
      (WilsonConditionalTaylorPurchase.Inventory u V R.kit ∧ Due (roster G) u V R.kit ∧
        Paid (atlas (fees V cle simple)) R.kit) ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧
      PhysicalNext.Repeat.Legato.Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨R,T,W,⟨outside,issued,fluct,rooted⟩,inventory,posterior,corr,base,citizen,logBook⟩ :=
    WilsonConditionalTaylorPosterior.select.{u} simple hε u V cle
      (Together (@more) (Together (@Due G _ _ (roster G) u V) (Together
        (@Paid G (atlas (fare V cle simple))) (@Paid G (atlas (fees V cle simple))))))
      (fun s M => joint (credit s M) (joint
        (WilsonConditionalTaylorFieldPurchase.prepaid (roster G) simple u V cle s _) (joint
        (WilsonConditionalTaylorThreshold.prepaid (atlas (fare V cle simple)) s _)
        (WilsonConditionalTaylorThreshold.prepaid (atlas (fees V cle simple)) s _))))
  exact ⟨R,T,W,outside,posterior,masks R simple u V cle inventory issued fluct,
    ⟨inventory,issued,rooted⟩,corr,base,citizen,logBook⟩

theorem select (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (u : G.ColorIndex)
    (V : Voice G) (cle : Clear G V) (more : Prediction G)
    (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      more R.kit ∧ WilsonConditionalTaylorPosterior.Posterior R u ∧
      (∀ a : Roster G, FluctuationMaskReadings (lamps a) R u) ∧
      (∀ e : Entry G, AllOrders e R u) ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧
      PhysicalNext.Repeat.Legato.Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨R,T,W,outside,posterior,fluct,⟨inventory,issued,cash⟩,corr,base,citizen,logBook⟩ :=
    presold.{u} simple hε u V cle more credit
  exact ⟨R,T,W,outside,posterior,fluct,original R simple u V cle inventory issued cash,corr,base,citizen,logBook⟩

end YM.Integration.WilsonPosteriorProjectionRootedSchedule
end

