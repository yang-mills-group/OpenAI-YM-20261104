import YM.Integration.WilsonConditionalTaylorFields
import YM.Integration.WilsonConditionalTaylorFieldPurchase
import YM.Integration.WilsonConditionalTaylorPurchase
import YM.Integration.WilsonWindowJointPurchase
import YM.Integration.WilsonConditionalTaylorCalendar
import YM.Integration.WilsonPosteriorProjectionRootedRoster
import YM.Integration.WilsonPosteriorProjectionRootedCharge
import YM.Integration.WilsonPosteriorProjectionThermalWindow
import YM.Integration.FVA1Physical.Round2.RootedFieldTrajectory

/-! All template invoices and the original full rooted physical field on an already selected run. The continuum selector with a free presale is composed separately. -/
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
open WilsonPosteriorProjectionPinned WilsonPosteriorProjectionRootedRoster
open RGComparison.Core16.Spool
open scoped Classical Topology BigOperators

variable {G : Gauge}

/-- Identical finite list and mask as the physical calendar's roster. -/
abbrev template (G : Gauge) (n : ℕ) : ↥(entry G n).2 → Lamp G := packet (entry G n)

def fees (V : Voice G) (cle : Clear G V) (hG : G.Simple) : ℕ → MapPrices → Fare :=
  fun n M H H' P K => max (readingMenu (template G n) V cle hG H H' P K)
    (max (emissionMenu (template G n) V cle hG M H H' P K)
      (max (rootedFieldMenu (cover (entry G n)) H H' P K)
        (WilsonPosteriorProjectionThermalWindow.changeFee G H H' P K)))

theorem invoices (R : Run G) (V : Voice G) (cle : Clear G V) (hG : G.Simple)
    (cash : Paid (atlas (fees V cle hG)) R.kit) (t : ℕ) :
    Late R (readingMenu (template G t) V cle hG) ∧
    Late R (emissionMenu (template G t) V cle hG R.metals.K) ∧
    Late R (rootedFieldMenu (cover (entry G t))) := by
  have paid := WilsonConditionalTaylorCalendar.read R (fees V cle hG) cash t
  exact ⟨paid.mono fun _ hj n => (le_max_left _ _).trans (hj n),
    paid.mono fun _ hj n => ((le_max_left _ _).trans (le_max_right _ _)).trans (hj n),
    paid.mono fun _ hj n => ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans (hj n)⟩

theorem clockInterval (R : Run G) (V : Voice G) (cle : Clear G V) (hG : G.Simple)
    (cash : Paid (atlas (fees V cle hG)) R.kit) :
    Late R (WilsonPosteriorProjectionThermalWindow.changeFee G) :=
  (WilsonConditionalTaylorCalendar.read R (fees V cle hG) cash 0).mono fun _ hj n =>
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans (hj n)

abbrev AllOrders (e : Entry G) (R : Run G) (u : G.ColorIndex) :=
  ∀ p q s L radius : ℕ, 0 < q → 6 ≤ s → ∀ {D η : ℝ}, 0 ≤ D → 0 < η →
    CurrentRooted (cover e) R u p q s L radius D η

theorem enrollment (R : Run G) (hG : G.Simple) (u : G.ColorIndex) (V : Voice G) (cle : Clear G V)
    (inventory : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
    (issued : Due (template G) u V R.kit) (cash : Paid (atlas (fees V cle hG)) R.kit) (n : ℕ) :
    PinnedReadings (template G n) R u ∧ PinnedEmissions (template G n) R u ∧
    Late R (rootedFieldMenu (cover (entry G n))) := by
  obtain ⟨frame,_,vac⟩ := inventory
  obtain ⟨reader,writer,spatial⟩ := invoices R V cle hG cash n
  exact ⟨WilsonPosteriorProjectionPinned.readings (template G n) hG R u V cle frame reader
      (WilsonConditionalTaylorFields.ports (template G) n hG R u V issued vac) vac,
    WilsonPosteriorProjectionPinned.emissions (template G n) hG R u V cle frame writer vac,spatial⟩
  
theorem original (R : Run G) (hG : G.Simple) (u : G.ColorIndex) (V : Voice G) (cle : Clear G V)
    (inventory : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
    (issued : Due (template G) u V R.kit) (cash : Paid (atlas (fees V cle hG)) R.kit) :
    ∀ e : Entry G, AllOrders e R u := by
  have eachCode (n : ℕ) : AllOrders (entry G n) R u := by
    obtain ⟨reads,rows,spatial⟩ := enrollment R hG u V cle inventory issued cash n
    have words := physical_field_words (template G n) hG R u reads rows
    intro p q s L radius hq hs D η hD hη
    obtain ⟨m,hm⟩ := margin_eventually (derivative_clock p 0 0 le_rfl hη).1
    exact physical_rooted_on (cover (entry G n)) R u hG V cle words rows p q s L radius hq hs
      hD hη (margin_pos m) hm (charge _ R spatial q (s+s) radius m)
  intro e
  simpa only [recover_entry] using eachCode (Encodable.encode e)

end YM.Integration.WilsonPosteriorProjectionRootedSchedule
end

