import YM.Integration.ActualRunRetunedVacuum

/-! The same retuned list has a fixed-order scalar budget. Only the upper
budget changes: every scaled atom, per-row cost, support and cover remains
the original one from GradedVacuumLayerRescaling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRetunedVacuumUniformCost
open Filter Lattice Wilson RG
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02
open scoped Topology

/-- Both inverse-square and positive-order scaling are paid by a fixed
fourth-base power. In particular negative step orders are retained. -/
theorem factorBound_le {ratio : ℝ} {order : ℕ} (horder : 2 ≤ order)
    (hlo : (1/4 : ℝ) ≤ ratio) (hhi : ratio ≤ 4) :
    NativeVacuumLayerRescaling.factorBound ratio order ≤ (4 : ℝ)^order := by
  have hr : 0 < ratio := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/4) hlo
  unfold NativeVacuumLayerRescaling.factorBound
  apply max_le
  · calc
      ratio ^ (-2 : ℤ) = (ratio^2)⁻¹ :=
        zpow_neg_coe_of_pos ratio (by norm_num : 0 < (2:ℕ))
      _ ≤ ((1/4 : ℝ)^2)⁻¹ :=
        inv_anti₀ (by norm_num : (0:ℝ) < (1/4 : ℝ)^2)
          (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) hlo 2)
      _ = (4 : ℝ)^2 := by norm_num
      _ ≤ (4 : ℝ)^order := pow_le_pow_right₀ (by norm_num) horder
  · calc
      ratio ^ (order : ℤ) = ratio^order := zpow_natCast ratio order
      _ ≤ (4 : ℝ)^order := pow_le_pow_left₀ hr.le hhi order

/-- This retains the complete existing scaled receipt, enlarging only its
total and cover-cost upper bounds. Its own-factor pieceCost is unchanged. -/
def graded {G : Gauge} {n : Side} {L : List (Piece G n)} {p : BudgetPoint}
    {order rankCap : ℕ} {width budget ratio : ℝ}
    (H : GradedVacuumLayers L p order rankCap width budget)
    (horder : 2 ≤ order) (hlo : (1/4 : ℝ) ≤ ratio) (hhi : ratio ≤ 4) :
    GradedVacuumLayers (NativeVacuumLayerRescaling.layers ratio L)
      p order rankCap width ((4 : ℝ)^order * budget) := by
  have hr : 0 < ratio := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/4) hlo
  let H' := GradedVacuumLayerRescaling.graded H hr
  have hb : 0 ≤ budget := (Real.exp_pos _).le.trans H.packets.cover_cost
  have hcost := mul_le_mul_of_nonneg_right (factorBound_le horder hlo hhi) hb
  exact {
    packets := { H'.packets with
      total := H'.packets.total.trans hcost
      cover_cost := H'.packets.cover_cost.trans hcost }
    orders := H'.orders
    leading_rank := H'.leading_rank }

end YM.Integration.ActualRetunedVacuumUniformCost
end
