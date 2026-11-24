import YM.Gauge.Casimir
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The tariff meter in r

This is B line 24, positive on the small positive lengths. Not the measured coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set Real Asymptotics
open scoped Topology

/-- Slope = 2 b₀. -/
def meter (G : Gauge) (r : ℝ) : ℝ := (Real.sqrt (G.slopeConstant*log r⁻¹))⁻¹

section positivity
variable {G : Gauge} (h : G.Simple)
local notation "g" => meter G
local notation "l" => (𝓝[>] (0:ℝ))
include h
lemma zooms : Tendsto (fun r : ℝ => G.slopeConstant * log r⁻¹) l atTop :=
  (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop (G.slopeConstant_pos h)
lemma warmG : ∀ᶠ r in l, 0 < g r := ((zooms h).eventually_gt_atTop (0:ℝ)).mono
  (fun r hr=> inv_pos.mpr (Real.sqrt_pos.mpr hr))
lemma endsG : Tendsto g l (𝓝 0) := tendsto_inv_atTop_zero.comp
  (Real.tendsto_sqrt_atTop.comp (zooms h))
variable {t : ℝ → ℝ}
lemma thermalO (ht : Tendsto (fun r=> t r / g r) l (𝓝 1)) : t =O[l] g := by
  apply IsBigO.of_bound 2
  have hu := ht.norm
  rw [norm_one] at hu
  filter_upwards [warmG h, hu.eventually (gt_mem_nhds (one_lt_two : (1:ℝ)<2))] with r hr hv
  rw [Real.norm_of_nonneg hr.le]
  have hv' : ‖t r / g r‖ < 2 := hv
  rw [norm_div, Real.norm_of_nonneg hr.le, div_lt_iff₀ hr] at hv'
  exact hv'.le
lemma twoPrices (ht : Tendsto (fun r=> t r / g r) l (𝓝 1)) :
    ∀ᶠ r in l, 0 < g r ∧ |t r| ≤ 1 ∧ |t r| ≤ 2*g r := by
  have hx := (thermalO h ht).trans_tendsto (endsG h)
  have hu := ht.abs; rw [abs_one] at hu
  have hs : Tendsto (fun r=>|t r|) l (𝓝 0) := by simpa only [abs_zero] using hx.abs
  filter_upwards [warmG h, hu.eventually (gt_mem_nhds (one_lt_two : (1:ℝ)<2)),
    hs.eventually (gt_mem_nhds zero_lt_one)] with r hr hv hw
  refine ⟨hr, le_of_lt hw, ?_⟩
  have hv' : |t r/g r|<2 := hv
  rw [abs_div,abs_of_nonneg hr.le,div_lt_iff₀ hr] at hv'; exact hv'.le
end positivity
end YM.FVA2.GradedFar
