import YM.Integration.NativeStageLogarithmicPrice
import YM.Integration.ActualRunNativeComponentRecipe
import YM.Integration.FullQLocalNumericLogarithmicCost

/-! The existing payment also pays the original coarse stage.
Monotonicity is derived from the literal schedule increment, not an added
prefix-payment field. The resulting event is before all geometric data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCoarseStagePrice
open Filter Lattice RG Precision PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep
open scoped Topology

/-- The original hatted beta increases along its original schedule. -/
theorem hatBeta_mono {G : Gauge} (a : Levels G) (hG : G.Simple) :
    Monotone a.clock.hatBeta := by
  apply monotone_nat_of_le_succ
  intro i
  have hL : (1 : ℝ) < (a.S.block i).val := by
    exact_mod_cast (show 1 < (a.S.block i).val from
      lt_of_lt_of_le (by norm_num) (a.S.block_large i))
  have hinc := mul_nonneg (Gauge.slopeConstant_pos hG).le (Real.log_pos hL).le
  change a.clock.bar + G.slopeConstant * a.S.scale i ≤
    a.clock.bar + G.slopeConstant * a.S.scale (i + 1)
  rw [a.S.scale_succ]
  nlinarith only [hinc]

private theorem log_mono {G : Gauge} (a : Levels G) (hG : G.Simple) :
    Monotone (fun i => Real.log (a.clock.hatBeta i)) := by
  intro i j hij
  exact Real.log_le_log (zero_lt_one.trans (a.fits.delayed i))
    (hatBeta_mono a hG hij)

/-- The same post-length payment controls the actual coarse stage. -/
theorem coarse_stage {G : Gauge} {a : Levels G} (hG : G.Simple)
    {P X : MapPrices} {O : ChartRatio G}
    (hpaid : RG08.Yamen.Payment G P X O a) {i : ℕ} (hi : 0 < i) :
    NativeStageLogarithmicPrice.stageSum (a.params i) ≤
      Real.log (a.clock.hatBeta i) := by
  have h := NativeStageLogarithmicPrice.stageSum_le_log hpaid (i - 1)
  rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)] at h
  exact h.trans (log_mono a hG (Nat.sub_le i 1))

/-- One original-schedule event pays the whole coarse-stage sum and the
predecessor logarithm used by the original kinetic denominator. -/
theorem coarse_cost {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} {J : Request V} (A : NumericSchedule T.family J) :
    ∀ᶠ i : ℕ in atTop, 0 < i ∧
      NativeStageLogarithmicPrice.stageSum (T.family.path.levels.params i) ≤
        A.admittedCost i ∧
      Real.log (T.family.path.levels.clock.hatBeta (i - 1)) ≤ A.admittedCost i := by
  obtain ⟨s, Q, choice, lengths, _hbase, _hfloor, _hsheet, hquote,
    _hnum, _hpost, _hstage, hReal⟩ := hT
  have hpaid := hReal.payment
  rw [← hquote] at hpaid
  filter_upwards [A.logarithmic_cost hG 1 1, eventually_gt_atTop 0]
    with i hlog hi
  have hnext := (Real.log_pos (T.family.path.levels.fits.delayed (i + 1))).le
  have hcurrent : Real.log (T.family.path.levels.clock.hatBeta i) ≤
      A.admittedCost i := by
    simp only [one_mul, pow_one] at hlog
    linarith
  exact ⟨hi, (coarse_stage hG hpaid hi).trans hcurrent,
    (log_mono T.family.path.levels hG (Nat.sub_le i 1)).trans hcurrent⟩

end YM.Integration.ActualCoarseStagePrice
end
