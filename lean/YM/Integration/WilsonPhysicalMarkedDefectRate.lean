import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import YM.Ac.Tree

/-! Conversion of the genuine common-window radius charge to the true fine
coupling. The threshold precedes all choices of such charges. -/

namespace YM.Integration.WilsonPhysicalMarkedDefect
open Filter

theorem coupling_rate (β : ℝ) (hβ : 0 < β) (r : ℝ) :
    (Real.sqrt β)⁻¹ ^ r = β^(-r/2) := by
  rw [Real.inv_rpow (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,←Real.rpow_mul hβ.le,←Real.rpow_neg hβ.le]
  congr 1
  ring

theorem restored_rate (C r t ε : ℝ) (hC : 0 ≤ C) (gap : ε < (r-t)/2) :
    ∀ᶠ β : ℝ in atTop, ∀ (cost : ℝ), cost ≤ (4*β)^ε →
      C*cost*((Real.sqrt β)⁻¹ ^ r) ≤ (Real.sqrt β)⁻¹ ^ t := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr gap)).eventually_ge_atTop (C*(4:ℝ)^ε)] with β hβ charge
  intro cost bound
  rw [coupling_rate β hβ r,coupling_rate β hβ t]
  calc
    C*cost*β^(-r/2) ≤ C*((4*β)^ε)*β^(-r/2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left bound hC) (Real.rpow_nonneg hβ.le _)
    _ = (C*(4:ℝ)^ε)*β^(ε+(-r/2)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hβ.le,Real.rpow_add hβ]
      ring
    _ ≤ β^((r-t)/2-ε)*β^(ε+(-r/2)) := mul_le_mul_of_nonneg_right charge (Real.rpow_nonneg hβ.le _)
    _ = β^(-t/2) := by rw [←Real.rpow_add hβ]; congr 1; ring

end YM.Integration.WilsonPhysicalMarkedDefect

