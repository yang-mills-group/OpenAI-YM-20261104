import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace YM.Integration.WilsonLogarithmicFourthPower

theorem logarithmicNumerator (m : ℕ) :
    Tendsto (fun r : ℝ => r ^ 4 * (Real.log r⁻¹) ^ m) (𝓝[>] 0) (𝓝 0) := by
  have price := (isLittleO_log_rpow_rpow_atTop (m : ℝ) (by norm_num : (0 : ℝ) < 4)).tendsto_div_nhds_zero
  have composed := price.comp tendsto_inv_nhdsGT_zero
  simpa [Function.comp_def, Real.rpow_natCast, div_eq_mul_inv, inv_pow, mul_comm] using composed

theorem fromRunning {θ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (positive : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < θ r)
    (vanishes : Tendsto θ (𝓝[>] 0) (𝓝 0))
    (running : Tendsto (fun r : ℝ => Real.log r⁻¹ * θ r ^ 2) (𝓝[>] 0) (𝓝 c))
    (m : ℕ) : (fun r : ℝ => r ^ 4) =o[𝓝[>] 0] (fun r => θ r ^ m) := by
  have diverges : Tendsto (fun r : ℝ => Real.log r⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have fraction := ((logarithmicNumerator m).div (running.pow m) (pow_ne_zero m hc.ne')).mul (vanishes.pow m)
  have result : Tendsto (fun r : ℝ => r ^ 4 / θ r ^ m) (𝓝[>] 0) (𝓝 0) := by
    have normalized : Tendsto (fun r : ℝ =>
        (r ^ 4 * Real.log r⁻¹ ^ m) / ((Real.log r⁻¹ * θ r ^ 2) ^ m) * θ r ^ m)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [Pi.div_apply, zero_div, zero_mul] using fraction
    apply normalized.congr'
    filter_upwards [positive, diverges.eventually_gt_atTop 0] with r hθ hlog
    change r ^ 4 * Real.log r⁻¹ ^ m / ((Real.log r⁻¹ * θ r ^ 2) ^ m) * θ r ^ m =
      r ^ 4 / θ r ^ m
    rw [mul_pow, ← pow_mul, Nat.mul_comm 2 m, pow_mul]
    field_simp [pow_ne_zero m hlog.ne', pow_ne_zero m hθ.ne'] <;> ring
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hlog.ne', one_pow, mul_one]
  apply IsLittleO.of_bound
  intro ε hε
  have small := result.norm.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [small, positive] with r hr hθ
  have inequality : ‖r ^ 4‖ / ‖θ r ^ m‖ ≤ ε := by simpa only [norm_div] using hr.le
  exact (div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero m hθ.ne'))).mp inequality

end YM.Integration.WilsonLogarithmicFourthPower
