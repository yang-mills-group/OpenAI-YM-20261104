import YM.Integration.NativeStageLogarithmicPrice
import YM.Integration.NativeCappedPathBounds
import YM.Integration.NativePolynomialSquarePay
import YM.Integration.ActualUniformAllCostPolynomial
import YM.Integration.ActualRunNativeComponentRecipe
import YM.Integration.RunRG02Along
import YM.RG12SharpGram.Fence.Paddock

/-! # The full stationary bill on the original Run

The same retained postnumeric payment bounds the original block and every
term of the original stage sum by log(hatBeta i).  Only the auxiliary
analytic width is reduced.  The actual path, path budget, clip, kernel and
period remain unchanged.  The one level tail is chosen before both N and
the period; it uses the existing J-versus-block event.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunStationaryCost

open Filter Lattice RG Precision Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Topology Classical Matrix.Norms.Frobenius

private theorem block_le_log {G : Gauge} {a : Levels G}
    {P X : MapPrices} {O : ChartRatio G}
    (hpaid : RG08.Yamen.Payment G P X O a) (i : ℕ) :
    ((a.S.block i).val : ℝ) ≤ Real.log (a.clock.hatBeta i) := by
  exact (RG08.Yamen.stamped G P X a.clock.kernel O
    (RG08.Supplies.stone a i)).length.trans (RG08.Yamen.hatch hpaid i)

/-- The original path has its full stationary bill bounded by one fixed
power of the original logarithmic stamp.  No new payment or analytic
estimate is a premise. -/
theorem stationary_log_cost {G : Gauge} (T : Run G)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    (n : ℕ) (Z K W : ℝ) :
    let a := T.family.path.levels
    ∃ A : ℝ, 0 < A ∧ ∃ d : ℕ,
      ∀ᶠ i : ℕ in atTop, ∀ N period : ℕ, i + 1 ≤ N →
        let Y := a.params (i + 1)
        let μ := NativeCappedPathBounds.cappedWidth Y.width (a.clock.J (i + 1))
        let X := (2 : ℝ)^n * (1 + (Y.paths * rootsCost G Z μ n)^2)
        (T.family.path.rep N period (i + 1)).path.Bounds
          Y.clip μ Y.paths (a.clock.loopCap (i + 1)) ∧
        SquarePay G n Z μ Y.paths X ∧
        allCost G n Z X μ Y.paths K W Y.clip
          (a.clock.op i period).patch a.clock.kernel ≤
            A * (Real.log (a.clock.hatBeta i))^d := by
  dsimp only
  let a := T.family.path.levels
  obtain ⟨A, hA, d, hcost⟩ :=
    ActualUniformAllCostPolynomial.allCost_square_polynomial
      G n Z K W a.clock.kernel
  refine ⟨A * (10 : ℝ)^d, mul_pos hA (pow_pos (by norm_num) _), d, ?_⟩
  obtain ⟨s, Q, choice, lengths, _hbase, _hfloor, _hsheet, hquote,
    _hnum, _hpost, _hstage, hReal⟩ := hT
  have hpaid := hReal.payment
  rw [← hquote] at hpaid
  filter_upwards [RG12SharpGram.Fence.window_slope (A := a) 1 (by norm_num)]
    with i hi
  intro N period hN
  let Y := a.params (i + 1)
  let μ := NativeCappedPathBounds.cappedWidth Y.width (a.clock.J (i + 1))
  let X := (2 : ℝ)^n * (1 + (Y.paths * rootsCost G Z μ n)^2)
  let L : ℝ := (a.S.block i).val
  let H := Real.log (a.clock.hatBeta i)
  let B := 1 + Y.paths + |Y.clip.direct| + L + (a.clock.J (i + 1) : ℝ) + μ⁻¹
  have hwidth := NativeCappedPathBounds.capped_facts Y.width_pos (a.clock.J (i + 1))
  have hμ : 0 < μ := hwidth.1
  have hpath := T.alloy.B.support.cap N (i + 1) hN
  rw [← CommonConstruction.runAlong_actual_path T N (i + 1) period hN] at hpath
  have hrestricted :
      (T.family.path.rep N period (i + 1)).path.Bounds
        Y.clip μ Y.paths (a.clock.loopCap (i + 1)) :=
    NativeCappedPathBounds.restrict_width hpath hμ hwidth.2.1
  have hdir : |Y.clip.direct| ≤ 1 := by
    rw [abs_of_pos Y.clip.quadratic_pos]
    exact NativeCappedPathBounds.direct_le_one hpath
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
  have hY : Y.paths ≤ H ∧ Y.width⁻¹ ≤ H := by
    have hp := Y.paths_pos
    have hw := inv_pos.mpr Y.width_pos
    have hc := Y.columns_ge
    have hr := Y.clip.radius_pos
    have he := Y.price_pos
    change NativeStageLogarithmicPrice.stageSum Y ≤ H at hstage
    dsimp only [NativeStageLogarithmicPrice.stageSum] at hstage
    constructor <;> linarith
  have hμinv : μ⁻¹ ≤ Y.width⁻¹ + ((a.clock.J (i + 1) : ℝ) + 3) :=
    hwidth.2.2.2
  have hbase : B ≤ 10 * H := by
    dsimp only [B]
    linarith only [hY.1, hY.2, hdir, hL, hJH, hHone, hμinv]
  have hpaths := Y.paths_pos
  have hLzero : 0 ≤ L := zero_le_one.trans hLone
  have hBzero : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hcap : μ * (((a.clock.op i period).patch.J : ℝ) + 3) ≤ 1 := by
    change μ * ((a.clock.J (i + 1) : ℝ) + 3) ≤ 1
    exact hwidth.2.2.1
  have hfull :
      allCost G n Z X μ Y.paths K W Y.clip
        (a.clock.op i period).patch a.clock.kernel ≤ A * B^d :=
    hcost (a.clock.op i period).patch μ Y.paths Y.clip
      Y.paths_pos.le hμ hcap
  refine ⟨hrestricted, NativePolynomialSquarePay.native_square_pay G n Z μ Y.paths, ?_⟩
  change allCost G n Z X μ Y.paths K W Y.clip
    (a.clock.op i period).patch a.clock.kernel ≤ (A * (10 : ℝ)^d) * H^d
  calc
    _ ≤ A * B^d := hfull
    _ ≤ A * (10 * H)^d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBzero hbase d) hA.le
    _ = _ := by rw [mul_pow]; ring

end YM.Integration.ActualRunStationaryCost
end
