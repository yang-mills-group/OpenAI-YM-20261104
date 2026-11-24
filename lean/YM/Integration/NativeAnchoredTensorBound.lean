import YM.Integration.NativeAnchoredAtomPrice

/-! The complete original one-port tensor sum has one fixed reciprocal-width
polynomial bound. The constant is chosen before the period, list, width and
all distinguished coordinates; every original list occurrence is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeAnchoredTensorBound

open Function Filter Set Metric Lattice Wilson RG Precision Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Comparison.RG02.Assembly Push.Uniform NativeAtomTensorLocality
open NativeAnchoredAtomBudget
open scoped Topology BigOperators ContDiff Classical

/-- All original roots, atoms and free coordinates are charged without a volume factor. -/
theorem total_polynomial (G : Gauge) (rankCap d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {s : Side} {layers : List (Piece G s)} {p : BudgetPoint}
      {order : ℕ} {width budget : ℝ}
      (H : GradedVacuumLayers layers p order rankCap width budget),
      0 < width → ∀ (j : Fin (d + 1)) (i0 : Index G s),
      (layers.map fun a => ∑ q : Fin d → Index G s, ∑' i : ℕ,
        ‖tensor (H.packets.atom a i) (a.packet.labels i).site (d + 1)
          (Fin.insertNth j i0 q)‖).sum ≤
        budget * C * (1 + width⁻¹) ^ (7 * (d + 1)) := by
  obtain ⟨C, hC, hP⟩ := NativeAnchoredAtomPrice.exists_port_polynomial G rankCap d
  refine ⟨C, hC, ?_⟩
  intro s layers p order width budget H hw j i0
  have hcost : 0 ≤ (layers.map H.packets.pieceCost).sum := by
    apply List.sum_nonneg
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact Extra.Iteration.Cost.nonneg (H.packets.exponential a ha (location i0))
  have hbudget : 0 ≤ budget := hcost.trans H.packets.total
  calc
    _ ≤ budget * portFactor G rankCap d width := total_anchored H hw d j i0
    _ ≤ budget * (C * (1 + width⁻¹) ^ (7 * (d + 1))) :=
      mul_le_mul_of_nonneg_left (hP width hw) hbudget
    _ = _ := (mul_assoc budget C ((1 + width⁻¹) ^ (7 * (d + 1)))).symm

end YM.Integration.NativeAnchoredTensorBound
end
