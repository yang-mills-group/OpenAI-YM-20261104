import YM.Euclid.Comparator

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
variable {G: Gauge} {d: ℕ}
def BottomOnly (G : Gauge) := Submodule.span ℂ ({1} : Set (WickPol G))
lemma unit_fits : BottomOnly G ≤ shellSector G d := by
  rw [BottomOnly,Submodule.span_le]; rintro u h
  obtain rfl : u=(1:WickPol G) := h
  exact ⟨Labels.unit G d, map_one reduceEq⟩
lemma unit_mem (G : Gauge) : 1 ∈ BottomOnly G := Submodule.subset_span rfl
end YM.Maxwell.Free
