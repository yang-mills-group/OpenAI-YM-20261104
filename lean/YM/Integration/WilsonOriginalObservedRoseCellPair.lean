import YM.Integration.WilsonOriginalObservedRoseFaces

/-! The original and independent grids can be tested on the same physical positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseCellPair

open Function Filter Finset Set MeasureTheory Lattice Maxwell XSpace
open WilsonSeparatedOriginalThermometerCells (weight tested)
open scoped Classical BigOperators

variable {I H : Type} [Fintype I] [Fintype H] [MeasurableSpace I] [MeasurableSpace H]
    [MeasurableSingletonClass I] [MeasurableSingletonClass H]
    (φ : Test 3) (χ : Points 3 → I) (γ : Points 3 → H)

def mass (p : I × H) : ℂ := weight φ (fun x=>(χ x,γ x)) p

theorem left (hc : Measurable χ) (hg : Measurable γ) (F : I → ℂ) :
    ∑i,weight φ χ i*F i=∑p:I×H,mass φ χ γ p*F p.1 := by
  rw [←tested φ χ hc F]
  exact tested φ (fun x=>(χ x,γ x)) (hc.prodMk hg) (fun p=>F p.1)

theorem right (hc : Measurable χ) (hg : Measurable γ) (F : H → ℂ) :
    ∑j,weight φ γ j*F j=∑p:I×H,mass φ χ γ p*F p.2 := by
  rw [←tested φ γ hg F]
  exact tested φ (fun x=>(χ x,γ x)) (hc.prodMk hg) (fun p=>F p.2)

/-- One variation budget suffices for the entire refined signed quadrature. -/
theorem variation (hc : Measurable χ) (hg : Measurable γ) :
    ∑p:I×H, ‖mass φ χ γ p‖ ≤ ∫x:Points 3,‖φ x‖ :=
  WilsonSeparatedOriginalThermometerCells.variation φ _ (hc.prodMk hg)

end YM.Integration.WilsonOriginalObservedRoseCellPair
