import YM.Integration.NativeAnchoredTensorBound
import Mathlib.Data.Fintype.Prod

/-! Exact conversion from a free-coordinate sum to the full fixed-port
indicator marginal. No symmetry, ordering quotient or cardinal factor is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeAnchoredTensorMarginal

open Function Filter Set Metric Lattice Wilson RG Precision Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Comparison.RG02.Assembly Push.Uniform NativeAtomTensorLocality
open scoped Topology BigOperators ContDiff Classical

/-- Fixing one coordinate is exactly the insertNth parametrization. -/
theorem sum_fixed {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ)
    (j : Fin (d + 1)) (i0 : I) (F : (Fin (d + 1) → I) → ℝ) :
    (∑ z : Fin (d + 1) → I, if z j = i0 then F z else 0) =
      ∑ q : Fin d → I, F (Fin.insertNth j i0 q) := by
  rw [← (Fin.insertNthEquiv (fun _ : Fin (d + 1) => I) j).sum_comp
    (fun z => if z j = i0 then F z else 0)]
  change (∑ p : I × (Fin d → I),
    if Fin.insertNth (α := fun _ : Fin (d + 1) => I) j p.1 p.2 j = i0
      then F (Fin.insertNth (α := fun _ : Fin (d + 1) => I) j p.1 p.2) else 0) = _
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp

/-- The literal full indicator marginal of every original atom has the same bill. -/
theorem total_marginal (G : Gauge) (rankCap d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {s : Side} {layers : List (Piece G s)} {p : BudgetPoint}
      {order : ℕ} {width budget : ℝ}
      (H : GradedVacuumLayers layers p order rankCap width budget),
      0 < width → ∀ (j : Fin (d + 1)) (i0 : Index G s),
      (layers.map fun a => ∑ z : Fin (d + 1) → Index G s,
        if z j = i0 then ∑' i : ℕ,
          ‖tensor (H.packets.atom a i) (a.packet.labels i).site (d + 1) z‖ else 0).sum ≤
        budget * C * (1 + width⁻¹) ^ (7 * (d + 1)) := by
  obtain ⟨C, hC, h⟩ := NativeAnchoredTensorBound.total_polynomial G rankCap d
  refine ⟨C, hC, ?_⟩
  intro s layers p order width budget H hw j i0
  simpa only [sum_fixed] using h H hw j i0

end YM.Integration.NativeAnchoredTensorMarginal
end
