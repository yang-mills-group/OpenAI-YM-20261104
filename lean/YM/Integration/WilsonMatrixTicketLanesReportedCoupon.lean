import YM.Integration.WilsonMatrixTicketLanesReportedPrepaid
import YM.Integration.WilsonMatrixTicketLanesReportedSettlement
import YM.Integration.WilsonCoherentInheritedPermit

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedCoupon
open Function Filter Real FVA2 FVA2.CityHistory Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open RGComparison.Core16 RGComparison.Core16.Spool PertExtension.Series.Tested
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedWords
open WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesReportedSettlement
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)

/-- The issued finite original power series for this very registered word. All
legs share the lower field, measured temperature, chart and forest. -/
def value {n m b N p : ℕ} (d : Fin n → ℕ) (q : ℕ) (elected : m=b+1)
    (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
    (u : Pins G (R.family.side b p)) (o : Fin n → Site (R.family.side m p))
    (tag : (step R p elected).Choices) (v : (Descent.nil (top:=R.family.side m p)).Tags)
    (j : ∀ i,(R.family.labels.level (d i)).Index) : ℂ :=
  peval (WilsonCoherentJointReturn.series (fun i=>WilsonCoherentTerminalFrame.lamp R (d i) (j i))
    (step R p elected) T R.metals.O u o large tag v) q (regulatorRun R.family N p m)

/-- Before any radius, upper cutoff, period or incoming field, the purchased
original run supplies a simultaneous numerical coupon for the entire coupled
fresh Wilson product at the inherited physical temperature. -/
theorem original (simple : G.Simple) (paid : Paid G R.kit) {n : ℕ} (d : Fin n → ℕ) (q cap : ℕ) :
    ∀ᶠ b : ℕ in atTop,∀ {f : Extraction.Order} {S : Table R.family.book}
      (F : Final R.family f S) (L : Layout F) (r : ℝ) (elected : L.level r=b+1)
      (w : ∀ i,R.family.label (d i)) (_age : ∀i,R.family.ref (d i) ≤ L.level r)
      (N p : ℕ) (_future : L.level r ≤ N) (large : Bid.Larger (G:=G) (step R p elected))
      (T : Forest (step R p elected).ratio) (u : Pins G (R.family.side b p))
      (o : Fin n → Site (R.family.side (L.level r) p)) (tag : (step R p elected).Choices)
      (v : (Descent.nil (top:=R.family.side (L.level r) p)).Tags), (∀ k,‖u k‖ ≤ (cap:ℝ)+1) →
      ‖fresh R F L r d w b N p elected u o -
        priced R F L r d w N p (value R (N:=N) d q elected large T u o tag v)‖ ≤
        (∏ i,(2:ℝ)^(d i)*mass R.family (d i) (L.shift (d i) r (w i))) *
          (regulatorRun R.family N p (L.level r)^(q+1) *
            (2+Real.log (R.family.path.levels.clock.hatBeta b))) := by
  have largeAt : ∀ b p,Bid.Larger (G:=G) (R.family.path.levels.clock.op b p) := paid.1
  have words (j : ∀ i,(R.family.labels.level (d i)).Index) :=
    WilsonCoherentInheritedPermit.purchased R (fun i=>WilsonCoherentTerminalFrame.lamp R (d i) (j i))
      ((cap:ℝ)+1) q start simple largeAt (paid.2 (code d j q cap))
  filter_upwards [eventually_all.mpr words] with b rows
  have held {m : ℕ} (elected : m=b+1) (N p : ℕ) (future : m≤N)
      (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
      (u : Pins G (R.family.side b p)) (o : Fin n → Site (R.family.side m p))
      (tag : (step R p elected).Choices) (v : (Descent.nil (top:=R.family.side m p)).Tags)
      (inside : ∀ k,‖u k‖≤(cap:ℝ)+1) (j : ∀i,(R.family.labels.level (d i)).Index) :
      ‖Spool.reads (fun i=>WilsonCoherentTerminalFrame.lamp R (d i) (j i)) (step R p elected)
          u o (regulatorRun R.family N p m) - value R (N:=N) d q elected large T u o tag v j‖ ≤
        regulatorRun R.family N p m^(q+1) * (2+Real.log (R.family.path.levels.clock.hatBeta b)) := by
    subst m
    exact rows j N p future T u o tag v inside
  intro f S F L r elected w age N p future large T u o tag v inside
  have heat : 0 ≤ regulatorRun R.family N p (L.level r) := inv_nonneg.mpr (Real.sqrt_nonneg _)
  exact WilsonMatrixTicketLanesReportedSettlement.measured R F L r d w b N p elected age future u o _ _
    (mul_nonneg (pow_nonneg heat _) (add_nonneg zero_le_two
      (Real.log_nonneg (R.family.path.levels.fits.delayed b).le)))
    (held elected N p future large T u o tag v inside)

end YM.Integration.WilsonMatrixTicketLanesReportedCoupon
