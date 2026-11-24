import YM.Integration.CommonStationaryQuotePurchase
import YM.Integration.ActualSpringStationaryService

/-! The stationary quote request evaluated on the same retained Run.
The numerical bill is independent of cutoff, period and chosen Spring packet;
this module does not claim any leading-column or equal-grade estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RunStationaryQuotePurchase

open Lattice RG Pressure
open PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat
open Progress.DirectedRecipe
open Push.PriceCompiler

variable {G : Gauge} (R : Run G)

/-- The preselection quote is literally the existing actual-service choice. -/
theorem quote_eq (m n : ℕ) :
    CommonStationaryQuotes.quote G
      (R.alloy.B.a.params (m + 1)).width (R.alloy.B.a.params (m + 1)).paths
      (R.alloy.B.a.clock.J (m + 1)) R.alloy.B.a.clock.kernel n =
        ActualSpringStationaryService.quotes R m n := rfl

/-- Evaluate the original chronological purchase at its literal two stage indices. -/
theorem earned_at
    (h : Mallow.RG12.Earned (CommonStationaryQuotePurchase.request G)
      R.kit.shape R.alloy.delay) (m : ℕ) :
    CommonStationaryQuotePurchase.Caps
      (Testing.query R.metals.p R.metals.K
        (R.alloy.B.a.clock.J (m + 1)) (R.alloy.B.a.clock.J m))
      (R.rolls.L (R.alloy.B.a.clock.J (m + 1)))
      (R.alloy.B.a.clock.hatBeta m) :=
  h _ _ (R.alloy.B.valid.pays m) _ (step_paid R.alloy.B.a m)

/-- All eligible requested orders use the same actual stationary table and clock. -/
theorem actual_bound
    (h : Mallow.RG12.Earned (CommonStationaryQuotePurchase.request G)
      R.kit.shape R.alloy.delay) (m n p : ℕ)
    (hn : n ≤ R.alloy.B.a.clock.J (m + 1)) :
    CommonStationaryQuotes.bill
      ((ActualSpringStationaryService.quotes R m n).tables
        (R.alloy.B.a.params (m + 1)).clip (R.alloy.B.a.clock.op m p).patch) ≤
      (R.alloy.B.a.clock.hatBeta m) ^
        ((1 : ℝ) / ((R.alloy.B.a.clock.J (m + 1) : ℝ) + 1)) := by
  have hL : (R.alloy.B.a.clock.op m p).patch.L =
      R.rolls.L (R.alloy.B.a.clock.J (m + 1)) := by
    change R.alloy.B.a.S.block m = _
    rw [← R.alloy.B.a.fits.sameFactor m, R.alloy.B.valid.lengths]
  have hp := params_eq R.alloy.B.valid (m + 1)
  have hκ := R.alloy.B.valid.kernel
  have hb := earned_at R h m n hn (R.alloy.B.a.clock.op m p).patch rfl hL
  rw [← quote_eq R m n, hp, hκ]
  exact hb

end YM.Integration.RunStationaryQuotePurchase
