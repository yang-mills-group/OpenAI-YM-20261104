import YangMills.WilsonProof.NativeSupport.YM.FVA2.Press.Deck
import YM.WilsonMS.Stencil.DualGrade

/-! The two independently constructed MS decks select the same Maxwell representatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange
open MS.Local.Physical

/-- Both nonnegative carriers are the image of the same on-shell lift of the
real bidegree sector, followed by its orbit in the quotient. -/
theorem continuumLimit_carrier (G : Gauge) (d r : ℕ) :
    FVA2.Press.born G d r = WilsonMS.Ensure.tangible G d r := by
  rfl

private theorem deck_eq_of_carries_eq {G : Gauge} {A B : Deck G}
    (h : A.carries = B.carries) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- Equality includes the shared choice of complement on each negative grade. -/
theorem continuumLimit_deck (G : Gauge) : FVA2.Press.portDeck G = WilsonMS.Ensure.deck G := by
  apply deck_eq_of_carries_eq
  funext d r
  cases d with
  | ofNat n => exact (FVA2.Press.level G n r).trans (continuumLimit_carrier G n r)
  | negSucc n => simp [FVA2.Press.portDeck, WilsonMS.Ensure.deck]

end YM.Integration.FVA1Physical.Exchange
