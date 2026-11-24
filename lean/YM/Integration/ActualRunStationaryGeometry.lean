import YM.Integration.NativeStageLogarithmicPrice
import YM.Integration.NativeCappedPathBounds
import YM.Integration.ActualRunNativeComponentRecipe
import YM.RG12SharpGram.Fence.Paddock

/-!
# The original capped stationary geometry is paid by the logarithmic stamp

The auxiliary width is the same literal cappedWidth as in stationary_log_cost.
One original J-versus-block event is chosen before every period. The block,
stage sum and width all use the retained payment on the same Run.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunStationaryGeometry

open Filter Lattice RG Precision
open PhysicalNext.Repeat.Legato
open scoped Topology Classical

private theorem block_le_log {G : Gauge} {a : Levels G}
    {P X : MapPrices} {O : ChartRatio G}
    (hpaid : RG08.Yamen.Payment G P X O a) (i : ℕ) :
    ((a.S.block i).val : ℝ) ≤ Real.log (a.clock.hatBeta i) :=
  (RG08.Yamen.stamped G P X a.clock.kernel O
    (RG08.Supplies.stone a i)).length.trans (RG08.Yamen.hatch hpaid i)

/-- The exact block-plus-reciprocal-width input of the joint-price polynomial.
The event precedes every period, and no new payment or width premise is used. -/
theorem capped_geometry {G : Gauge} (T : Run G)
    (hT : ActualRunNativeComponentRecipe.Attached T) :
    let a := T.family.path.levels
    ∀ᶠ i : ℕ in atTop, ∀ period : ℕ,
      let μ := NativeCappedPathBounds.cappedWidth
        (a.params (i + 1)).width (a.clock.J (i + 1))
      0 < μ ∧ μ ≤ 1 ∧
        1 + ((a.clock.op i period).patch.L.val : ℝ) + μ⁻¹ ≤
          7 * Real.log (a.clock.hatBeta i) := by
  dsimp only
  let a := T.family.path.levels
  obtain ⟨s, Q, choice, lengths, _hbase, _hfloor, _hsheet, hquote,
    _hnum, _hpost, _hstage, hReal⟩ := hT
  have hpaid := hReal.payment
  rw [← hquote] at hpaid
  filter_upwards [RG12SharpGram.Fence.window_slope (A := a) 1 (by norm_num)]
    with i hi
  intro period
  let Y := a.params (i + 1)
  let μ := NativeCappedPathBounds.cappedWidth Y.width (a.clock.J (i + 1))
  let L : ℝ := (a.S.block i).val
  let H := Real.log (a.clock.hatBeta i)
  have hwidth := NativeCappedPathBounds.capped_facts Y.width_pos (a.clock.J (i + 1))
  have hμ : 0 < μ := hwidth.1
  have hJ3 : (1 : ℝ) ≤ (a.clock.J (i + 1) : ℝ) + 3 := by
    have hJ0 := Nat.cast_nonneg (α := ℝ) (a.clock.J (i + 1))
    linarith
  have hμone : μ ≤ 1 := by
    calc
      μ = μ * 1 := (mul_one μ).symm
      _ ≤ μ * ((a.clock.J (i + 1) : ℝ) + 3) :=
        mul_le_mul_of_nonneg_left hJ3 hμ.le
      _ ≤ 1 := hwidth.2.2.1
  have hL : L ≤ H := block_le_log hpaid i
  have hJ : (a.clock.J (i + 1) : ℝ) ≤ L := by
    simpa only [one_mul] using hi.le
  have hLone : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast (show 1 ≤ (a.S.block i).val from by
      have := a.S.block_large i
      omega)
  have hHone : 1 ≤ H := hLone.trans hL
  have hJH : (a.clock.J (i + 1) : ℝ) ≤ H := hJ.trans hL
  have hstage := NativeStageLogarithmicPrice.stageSum_le_log hpaid i
  have hYwidth : Y.width⁻¹ ≤ H := by
    have hp := Y.paths_pos
    have hw := inv_pos.mpr Y.width_pos
    have hc := Y.columns_ge
    have hr := Y.clip.radius_pos
    have he := Y.price_pos
    change NativeStageLogarithmicPrice.stageSum Y ≤ H at hstage
    dsimp only [NativeStageLogarithmicPrice.stageSum] at hstage
    linarith
  have hμinv : μ⁻¹ ≤ Y.width⁻¹ + ((a.clock.J (i + 1) : ℝ) + 3) :=
    hwidth.2.2.2
  change 0 < μ ∧ μ ≤ 1 ∧ 1 + L + μ⁻¹ ≤ 7 * H
  refine ⟨hμ, hμone, ?_⟩
  linarith only [hYwidth, hL, hJH, hHone, hμinv]

end YM.Integration.ActualRunStationaryGeometry
end
