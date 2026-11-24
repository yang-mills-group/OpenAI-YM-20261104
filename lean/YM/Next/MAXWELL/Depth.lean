import YM.Euclid.Comparator
import YM.Next.MAXWELL.Covariance

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G: Gauge} {d: ℕ}
lemma closed_sector {p : WickPol G} (h : p∈shellSector G d) (s : Ortho) :
    reflectPol s p ∈ shellSector G d ∧ realForm p∈ shellSector G d := by
  obtain ⟨A,rfl⟩ := h; rw [← real_eats, ← pulls_label]; exact ⟨⟨_,rfl⟩,_,rfl⟩
end YM.Maxwell.Free
