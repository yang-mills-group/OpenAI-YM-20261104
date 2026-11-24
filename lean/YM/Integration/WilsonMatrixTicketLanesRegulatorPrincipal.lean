import YM.Integration.WilsonMatrixTicketLanesRegulatorWick
import YM.Integration.WilsonMatrixTicketLanesRegulatorIndependent

/-! The registered zero relative coefficient on the purchased original run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegulatorPrincipal
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Series Tested Radial PertExtension.GaussianScore
open FVA2 FVA2.CityHistory RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.Spool Next.Rank.Normal
open ThermalShortcuts.ThermalJets WilsonConditionalTaylorThermalCensus WilsonConditionalTaylorThermalBidScore
open WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedWords
open WilsonMatrixTicketLanesRegulatorIndependent MS.Local.Physical Next.Rank.Price WilsonMatrixTicketLanesNativePrices
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (R : Run G)

/-- The joint Gaussian contraction at this specific finite period and forest. -/
def contracted {n k b p : ℕ} (d : Fin n→ℕ) (elected : k=b+1)
    (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
    (o : Fin n→Site (R.family.side k p)) (tag : (step R p elected).Choices)
    (v : (Descent.nil (top:=R.family.side k p)).Tags) (j : ∀i,(R.family.labels.level (d i)).Index) (part : Bool) : ℝ :=
  let D := Descent.push (step R p elected) T Descent.nil
  let A := entries R.family d j (fun i=>CoefficientBridge.run_valuation R (d i))
  let L := fun h=>leg G D (face A o h) (color A h)
  let Γ := ambient (d:=D) (tag,v) (show D.Room G from ⟨large,trivial⟩)
  ∑ m ∈ rows A, bill A part m * (blend (FVA2.Wick.color Γ L) 0 (glyphs id (parties A m))).re

def gaussian {n k b p : ℕ} (d : Fin n→ℕ) (elected : k=b+1)
    (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
    (o : Fin n→Site (R.family.side k p)) (tag : (step R p elected).Choices)
    (v : (Descent.nil (top:=R.family.side k p)).Tags) (j : ∀i,(R.family.labels.level (d i)).Index) : ℂ :=
  ⟨contracted R d elected large T o tag v j false,contracted R d elected large T o tag v j true⟩

/-- One paid stage works simultaneously for every arity, engineering grade and placement. -/
theorem original (paid : Paid G R.kit) :
    ∀ᶠ b : ℕ in atTop,∀ (n k N p : ℕ) (d : Fin n→ℕ) (elected : k=b+1)
      (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
      (o : Fin n→Site (R.family.side k p)) (tag : (step R p elected).Choices)
      (v : (Descent.nil (top:=R.family.side k p)).Tags) (j : ∀i,(R.family.labels.level (d i)).Index),
      WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d 0 elected large T 0 o tag v j =
        gaussian R d elected large T o tag v j := by
  let empty : Menu G := code (n:=0) (fun _=>0) (fun i=>i.elim0) 0 0
  filter_upwards [paid.2 empty] with b sale
  obtain ⟨P,X,U,C,offer,_⟩ := sale
  intro n k N p d elected large T o tag v j
  subst k
  have first : WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d 0 rfl large T 0 o tag v j =
      WilsonCoherentJointReturn.series (WilsonMatrixTicketLanesDescentWords.lamps R d j) (step R p rfl)
        T R.metals.O 0 o large tag v 0 := by
    simp [WilsonMatrixTicketLanesReportedCoupon.value,peval,Zone.eval]
    rfl
  rw [first]
  have seen := WilsonMatrixTicketLanesRegulatorWick.original R d j (step R p rfl) T o X offer large tag v
  exact Complex.ext (seen false) (seen true)

/-- The independently specified lower angular corrections multiply these very contractions. -/
theorem filed (paid : Paid G R.kit) :
    ∀ᶠ b : ℕ in atTop,∀ (B : Deck G) (n k N p : ℕ) (d h : Fin n→ℕ) (w : ∀i,B.BIndex ((d i):ℤ) (h i))
      (elected : k=b+1) (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
      (o : Fin n→Site (R.family.side k p)) (tag : (step R p elected).Choices)
      (v : (Descent.nil (top:=R.family.side k p)).Tags),
      finite R B d h w k N p (WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d 0 elected large T 0 o tag v) =
        finite R B d h w k N p (gaussian R d elected large T o tag v) := by
  filter_upwards [original R paid] with b budget B n k N p d h w elected large T o tag v
  exact congrArg (finite R B d h w k N p) (funext (budget n k N p d elected large T o tag v))

end YM.Integration.WilsonMatrixTicketLanesRegulatorPrincipal
