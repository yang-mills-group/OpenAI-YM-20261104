import YM.Integration.ActualStartupInvoice
import YM.Integration.ActualRepeatedNorm

/-! A fixed explicit budget for the unchanged paid startup album.
The only width restriction is the actual chosen upper bound one. Native
Start.weight and the exact finite rank sum give a constant before all
cutoffs and periods. No original Piece.credit bound is used. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupAlbumBudget
open Lattice Wilson RG
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open ActualStartupVacuumPackets ActualStartupCurvaturePackets
open PhysicalNext.Repeat.Legato LocalComparison.Global
open scoped Classical BigOperators

variable {G : Gauge}

/-- Every original finite rank and the original support-cover tariff remain. -/
def budget (G : Gauge) (support : ℝ) (r : ℕ) : ℝ :=
  max (((List.range (r - 2)).map (fun j => layerCost G 1 1 (5 + j))).sum)
    (Real.exp (support * (5 ^ 4 : ℕ)))

theorem budget_positive (G : Gauge) (support : ℝ) (r : ℕ) :
    0 < budget G support r :=
  (Real.exp_pos _).trans_le (le_max_right _ _)

private theorem layer_le (u width : ℝ) (k : ℕ)
    (hu : |u| ≤ 1) (hw : width ≤ 1) :
    layerCost G u width k ≤ layerCost G 1 1 k := by
  have hc := coefficientCost_nonnegative G k
  have hm : |u| * coefficientCost G k ≤ |(1 : ℝ)| * coefficientCost G k := by
    simpa only [abs_one] using mul_le_mul_of_nonneg_right hu hc
  have he : Real.exp (width * (k * 6 : ℕ)) ≤
      Real.exp (1 * (k * 6 : ℕ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _))
  unfold layerCost rowCost
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul hm he (Real.exp_nonneg _)
      (mul_nonneg (abs_nonneg _) hc))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem album_le (Q : BudgetPoint) (S : Stage) (r : ℕ)
    (width : ℝ) (hw : width ≤ 1) (hclip : S.clip.direct ≤ 1) :
    albumCost G Q S r width ≤ budget G Q.supportExponent r := by
  have hu : |Start.weight S.clip 1| ≤ 1 := by
    simpa only [Real.norm_eq_abs, norm_one] using Start.weight_le (c := S.clip) 1 hclip
  have hs : ∀ L : List ℕ,
      (L.map (fun j => layerCost G (Start.weight S.clip 1) width (5 + j))).sum ≤
      (L.map (fun j => layerCost G 1 1 (5 + j))).sum := by
    intro L
    induction L with
    | nil => exact le_rfl
    | cons j L ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (layer_le _ _ _ hu hw) ih
  exact max_le_max (hs _) le_rfl

/-- The same constant pays every original startup stage and physical period. -/
theorem actual_album_le (R : Run G)
    (fieldOrder distanceOrder : ℕ) (support : ℝ)
    (hfield : 6 ≤ fieldOrder) (hdistance : 2 ≤ distanceOrder)
    (hsupport : 0 < support) (N r : ℕ) (width : ℝ) (hw : width ≤ 1) :
    albumCost G
      (ActualRepeatedNorm.atLevel R.family fieldOrder distanceOrder support
        hfield hdistance hsupport N)
      (R.family.path.levels.params N) r width ≤ budget G support r :=
  album_le _ _ _ _ hw
    (Push.PriceCompiler.Canonical.direct_le_one
      (R.alloy.B.support.cap N N le_rfl).metric)

/-- The actual paid album, including every zero and padded row, at the
fixed explicit budget. Increasing the advertised rank capacity changes
no atom, list, action, support, width, or numerical piece cost. -/
theorem paid_layers (R : Run G)
    (fieldOrder distanceOrder : ℕ) (support : ℝ)
    (hfield : 6 ≤ fieldOrder) (hdistance : 2 ≤ distanceOrder)
    (hsupport : 0 < support) (N period r rankCap : ℕ)
    (hrank : r + 2 ≤ rankCap) (width : ℝ)
    (hwidth : 0 ≤ width) (hw : width ≤ 1) :
    let Q := ActualRepeatedNorm.atLevel R.family fieldOrder distanceOrder support
      hfield hdistance hsupport N
    Nonempty (FullQLocal.GradedVacuumLayers
      (ActualStartupInvoice.paidAlbum G (R.family.side N period) Q
        (R.family.path.levels.params N) r width)
      Q r rankCap width (budget G support r)) := by
  dsimp only
  let Q := ActualRepeatedNorm.atLevel R.family fieldOrder distanceOrder support
    hfield hdistance hsupport N
  let H := ActualStartupInvoice.paidGradedAlbum G (R.family.side N period) Q
    (R.family.path.levels.params N) r width hwidth
  have hb := actual_album_le R fieldOrder distanceOrder support
    hfield hdistance hsupport N r width hw
  refine ⟨{
    packets := {
      atom := H.packets.atom
      rank_bounded := fun a ha => (H.packets.rank_bounded a ha).trans hrank
      invariant := H.packets.invariant
      original_action := H.packets.original_action
      support := H.packets.support
      pieceCost := H.packets.pieceCost
      piece_cost_nonnegative := H.packets.piece_cost_nonnegative
      exponential := H.packets.exponential
      total := H.packets.total.trans hb
      coverOffset := H.packets.coverOffset
      coverSlope := H.packets.coverSlope
      cover := H.packets.cover
      width_reserved := H.packets.width_reserved
      cover_cost := H.packets.cover_cost.trans hb }
    orders := H.orders
    leading_rank := H.leading_rank }⟩

end YM.Integration.ActualStartupAlbumBudget
end
