import YM.Integration.WilsonPosteriorProjectionPrescribed
import YM.Integration.WilsonPosteriorProjectionRootedSchedule

/-! One ordinary funded Yang–Mills continuum construction carrying the
full true nonlinear test of every fresh original finite census at every
coupling and angular grade, preserving an arbitrary additional presale. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionPrescribedSchedule

open Function Filter Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler Source Labels
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection Next.Foundations
open MSbar MSbar.Heath FVA1Physical.Wilson FVA1Physical.Round2.Curvature FVA1Physical.Marked
open WilsonConditionalTaylorLabels WilsonConditionalTaylorThreshold WilsonConditionalTaylorCalendar
open WilsonConditionalTaylorFieldPurchase WilsonWindowJointPurchase WilsonConditionalTaylorPhysical
open WilsonPosteriorProjectionRootedRoster WilsonPosteriorProjectionRootedSchedule WilsonPosteriorProjectionPinned
open RGComparison.Core16.Spool
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge}

abbrev Full (e : Entry G) (R : Run G) (u : G.ColorIndex) :=
  ∀ (H : Hol G) (J : Jet G) (d p K L radius : ℕ), ∀ {η : ℝ}, 0<η →
    WilsonPosteriorProjectionPrescribed.Thermal (cover e) R u H J d p K L radius η

private theorem testBooked (R : Run G) (hG : G.Simple) (u : G.ColorIndex) (V : Voice G)
    (cle : Clear G V) (e : Entry G) (reading : PinnedReadings (freshLamps (cover e)) R u)
    (emitter : PinnedEmissions (freshLamps (cover e)) R u)
    (rooted : Late R (rootedFieldMenu (cover e)))
    (window : Late R (WilsonPosteriorProjectionThermalWindow.changeFee G)) : Full e R u := by
  intro H J d p K L radius η hη
  cases K with
  | zero =>
    exact WilsonPosteriorProjectionPrescribed.value (cover e) R u hG reading emitter H J d p L radius hη
  | succ K =>
    exact WilsonPosteriorProjectionPrescribed.thermal (cover e) R u hG V cle reading emitter rooted
      window H J d p (K+1) L radius (Nat.succ_pos K) hη

theorem applyTo (R : Run G) (hG : G.Simple) (u : G.ColorIndex) (V : Voice G) (cle : Clear G V)
    (inventory : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
    (issued : Due (roster G) u V R.kit) (cash : Paid (atlas (fees V cle hG)) R.kit) :
    ∀ e : Entry G, Full e R u := by
  have window := clockInterval R V cle hG cash
  have eachCode (n : ℕ) : Full (entry G n) R u := by
    obtain ⟨reading,emitter,rooted⟩ := enrollment R hG u V cle inventory issued cash n
    exact testBooked R hG u V cle (entry G n) reading emitter rooted window
  intro e
  simpa only [recover_entry] using eachCode (Encodable.encode e)

theorem select (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (u : G.ColorIndex)
    (V : Voice G) (cle : Clear G V) (more : Prediction G)
    (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      more R.kit ∧ WilsonConditionalTaylorPosterior.Posterior R u ∧
      (∀ a : Roster G, FluctuationMaskReadings (lamps a) R u) ∧
      (∀ e : Entry G, AllOrders e R u) ∧ (∀ e : Entry G, Full e R u) ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧
      PhysicalNext.Repeat.Legato.Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨R,T,W,outside,posterior,fluct,⟨inventory,issued,cash⟩,corr,base,citizen,logBook⟩ :=
    presold.{u} simple hε u V cle more credit
  exact ⟨R,T,W,outside,posterior,fluct,original R simple u V cle inventory issued cash,
    applyTo R simple u V cle inventory issued cash,corr,base,citizen,logBook⟩

end YM.Integration.WilsonPosteriorProjectionPrescribedSchedule
end

