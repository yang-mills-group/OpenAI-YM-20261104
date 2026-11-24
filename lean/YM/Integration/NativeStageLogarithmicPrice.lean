import YM.RG08.Yamen.Penny

/-!
The original logCost condition already pays every term of its stage sum.
The existing post-length payment converts its block bound to a logarithmic
bound. All statements retain the supplied Levels and its original stages.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeStageLogarithmicPrice
open Lattice RG Precision
open scoped Classical

/-- The literal positive sum in Calendar.Fits.logCost. -/
def stageSum (p : Stage) : ℝ :=
  1 + p.paths + p.width⁻¹ + p.columns + p.clip.relaxation + p.supportExponent

private theorem stageSum_pos (p : Stage) : 0 < stageSum p := by
  have hp := p.paths_pos
  have hw := inv_pos.mpr p.width_pos
  have hc := p.columns_ge
  have hr := p.clip.radius_pos
  have he := p.price_pos
  dsimp [stageSum]
  linarith

/-- Exponentiating the actual logCost bound loses only its saving exponent. -/
theorem stageSum_le_block {G : Gauge} (a : Levels G) (i : ℕ) :
    stageSum (a.params (i + 1)) ≤ (a.S.block i).val := by
  have hL : (1 : ℝ) < (a.S.block i).val := by
    exact_mod_cast (show 1 < (a.S.block i).val from
      lt_of_lt_of_le (by norm_num) (a.S.block_large i))
  have hlog := Real.log_pos hL
  have hJ : (1 : ℝ) ≤ (a.clock.J (i + 1) : ℝ) := by
    exact_mod_cast (show 1 ≤ a.clock.J (i + 1) from
      (by norm_num : 1 ≤ 4).trans (a.clock.adm (i + 1)))
  have hs : (1 : ℝ) ≤ (a.clock.J (i + 1) : ℝ) ^ 2 := by
    nlinarith
  have hi : ((a.clock.J (i + 1) : ℝ) ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hs
  have hh : Real.log (stageSum (a.params (i + 1))) ≤
      ((a.clock.J (i + 1) : ℝ) ^ 2)⁻¹ *
        Real.log (a.S.block i).val :=
    (div_le_iff₀ hlog).mp (a.fits.logCost i)
  apply (Real.log_le_log_iff (stageSum_pos _) (zero_lt_one.trans hL)).mp
  exact hh.trans ((mul_le_mul_of_nonneg_right hi hlog.le).trans_eq
    (one_mul _))

/-- The same purchased post-length stamp pays inverse width and all peers. -/
theorem stageSum_le_log {G : Gauge} {a : Levels G}
    {P X : MapPrices} {Z : ChartRatio G}
    (hpaid : RG08.Yamen.Payment G P X Z a) (i : ℕ) :
    stageSum (a.params (i + 1)) ≤ Real.log (a.clock.hatBeta i) := by
  have hs := RG08.Yamen.stamped G P X a.clock.kernel Z (RG08.Supplies.stone a i)
  have hp := RG08.Yamen.hatch hpaid i
  exact (stageSum_le_block a i).trans (hs.length.trans hp)

end YM.Integration.NativeStageLogarithmicPrice
end
