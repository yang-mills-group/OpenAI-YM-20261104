import YM.Integration.WilsonMatrixTicketLanesDescentContractions
import YM.Integration.WilsonCoherentJointReturn
import YM.RGComparison.Core16.Spool.Boarding

/-! The flat-pin finite periodic coupon, on the same registered Wilson fields and forest. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegulatorWick
open Function Filter Lattice RG Tree Wilson Precision Push.BetaTransport PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Series Tested Radial PertExtension.GaussianScore
open FVA2 FVA2.CityHistory RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.Spool Next.Rank.Normal
open ThermalShortcuts.ThermalJets WilsonConditionalTaylorThermalCensus
open WilsonConditionalTaylorThermalBidScore WilsonMatrixTicketLanesDescentWords
open scoped Topology ContDiff BigOperators Classical

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] (k : I → ℕ)
    (i : ∀ s, (R.family.labels.level (k s)).Index) {N p : ℕ} {c : Side}
    (S : StepData c (R.family.side N p)) (T : Forest S.ratio) (x : I → Site (R.family.side N p))
local notation "D" => Descent.push S T Descent.nil

theorem registered : (D).Testable (column (lamps R k i) x) ∧ (D).grade (column (lamps R k i) x) (power (lamps R k i)) := by
  let f (s : I) := (R.family.localSection (k s)).places (Pi.single (i s) 1) (x s)
  have one (s : I) : (D).Testable (f s) ∧ (D).grade (f s) ((R.family.labels.level (k s)).grades (i s)).2 :=
    basis_test R.makes (CoefficientBridge.run_valuation R (k s)) D (x s) (i s)
  refine ⟨⟨tally_cont _ _,tally_invariant _ _,?_⟩,?_⟩
  · exact contDiffAt_prod (fun s _ => (one s).1.smooth)
  intro y
  let F (s : I) (r : ℝ) := f s ((D).fine 1 ((D).tablePath (r • y)))
  have charged := bill_product Finset.univ (fun s => ((R.family.labels.level (k s)).grades (i s)).2)
    F (fun s _ => (one s).2 y)
  obtain ⟨C,hC,ht⟩ := charged
  refine ⟨C,hC,?_⟩
  filter_upwards [ht] with r cost
  rw [Finset.prod_apply] at cost
  exact cost

variable {P : Parcel.Oven S.patch} (X : P.Form G) (offer : P.Offers X S.kernel)
    (large : Bid.Larger (G:=G) S) (tag : S.Choices) (nil : (Descent.nil (top:=R.family.side N p)).Tags)

include X offer

/-- The entire measured local coupon is the true zero-offset finite one-step conditional series. -/
theorem series : WilsonCoherentJointReturn.series (lamps R k i) S T R.metals.O 0 x large tag nil =
    WilsonXLocal.kernel R.metals.O D 0 (column (lamps R k i) x) (power (lamps R k i)) := by
  have inside : ∀ a, ‖(0 : Pins G c) a‖ ≤ X.Q := by simp [offer.good.thick.1.le]
  have same := WilsonCoherentJointReturn.same (lamps R k i) S T R.metals.O 0 x large tag nil X R.alloy.B.ratio offer inside
  have seen := registered R k i S T x
  exact same.symm.trans (Spool.plain (lamps R k i) S T X R.metals.O x offer large R.alloy.B.ratio seen.1 seen.2)

/-- Each printed finite-period word uses its own full original signed face/color polynomial.
All contractions are taken in the actual finite-torus Hessian of this very one-step descent. -/
theorem original (part : Bool) :
    let A := entries R.family k i (fun s => CoefficientBridge.run_valuation R (k s))
    let L := fun s => leg G D (face A x s) (color A s)
    let Γ := ambient (d:=D) (tag,nil) (show (D).Room G from ⟨large,trivial⟩)
    look part (WilsonCoherentJointReturn.series (lamps R k i) S T R.metals.O 0 x large tag nil 0) =
      ∑ m ∈ rows A, bill A part m * (blend (FVA2.Wick.color Γ L) 0 (glyphs id (parties A m))).re := by
  rw [series R k i S T x X offer large tag nil]
  have h := (WilsonMatrixTicketLanesDescentContractions.original R k i D x R.metals.O R.alloy.B.ratio
    (show (D).Room G from ⟨large,trivial⟩) (tag,nil) 0 part).2
  cases part <;> exact h

end YM.Integration.WilsonMatrixTicketLanesRegulatorWick
