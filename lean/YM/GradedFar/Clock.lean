import YM.Gauge.Casimir

/-!
# The scalar interface to the pose-fit hypotheses

Only uses the stated outputs of PoseFit; it is not an assertion of PoseFit,
and in particular no assertion of the physical detector's calibration by the
*formal* theory. This spells out which hypotheses from the supplied mathematical
proof are needed for the second line of (M.2).
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Real Set
open scoped Topology

/-- Graded far-field coupling of §A, `(√ (2 b₀ log (1/r)))⁻¹`. -/
def gYM (G : Gauge) (r : ℝ) := (Real.sqrt (G.slopeConstant * Real.log r⁻¹))⁻¹

variable {G : Gauge} (simple : G.Simple)
local notation "g" => gYM G
local notation "τ" => 𝓝[>] (0:ℝ)

include simple
lemma log_kinetic : Tendsto (fun r : ℝ => G.slopeConstant * Real.log r⁻¹) τ atTop :=
  (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop (Gauge.slopeConstant_pos simple)
lemma shrink : Tendsto g τ (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (log_kinetic simple))
lemma positive_g : ∀ᶠ r in τ, 0 < g r := by
  filter_upwards [(log_kinetic simple).eventually_gt_atTop 0] with r hr
  exact inv_pos.mpr (Real.sqrt_pos.mpr hr)

/-- The hypothesis called on physical calibration is NOT from `Main.Match`. In
NearFarDelta it comes from PoseFit. PoseFit supplies `t'_ℓ∼g` (line 1337), and
(F.3), both for sufficiently large bookings `M` (`J=M-1` here), which imply
the following. -/
theorem relative_reading (t proxy : ℝ → ℝ)
    (hproxy : Tendsto (fun r : ℝ => proxy r / g r) τ (𝓝 1)) (J : ℕ) (hJ : 2 ≤ J) (C : ℝ)
    (hF3 : ∀ᶠ r in τ, |t r - proxy r| ≤ C * g r ^ J) :
    Tendsto (fun r => t r / g r) τ (𝓝 1) := by
  refine tendsto_of_tendsto_of_dist hproxy ?_
  have upper : Tendsto (fun r : ℝ => C * g r^(J-1)) τ (𝓝 0) := by
    simpa only [zero_pow (by omega : J-1 ≠ 0), mul_zero] using
      ((shrink simple).pow (J-1)).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun r => dist_nonneg) ?_ upper
  filter_upwards [hF3,positive_g simple] with r hr hg
  rw [dist_comm,Real.dist_eq,← sub_div, abs_div, abs_of_pos hg, div_le_iff₀ hg, mul_assoc,
    ← pow_succ, show J-1+1=J by omega]
  exact hr

/-- Alternative input convention for the calibration: positivity and the
specified construction's `Trace.Pilot.Coupling.running`.
Same argument as `WilsonMaxwellThermometerKineticLog.running`. -/
theorem relative_running (t : ℝ → ℝ) (he : ∀ᶠ r in τ, 0 < t r)
    (hr : Tendsto (fun r => Real.log r⁻¹*t r ^ 2) τ (𝓝 G.slopeConstant⁻¹)) :
    Tendsto (fun r => t r / g r) τ (𝓝 1) := by
  have hp := hr.const_mul G.slopeConstant
  rw [mul_inv_cancel₀ (Gauge.slopeConstant_pos simple).ne'] at hp
  have hu := hp.sqrt; rw [Real.sqrt_one] at hu
  refine hu.congr' ?_
  filter_upwards [he,(log_kinetic simple).eventually_gt_atTop 0] with r h hl
  change Real.sqrt _ = _ / _⁻¹
  rw [← mul_assoc,Real.sqrt_mul (show 0 ≤ G.slopeConstant * Real.log r⁻¹ from hl.le),
    Real.sqrt_sq h.le, div_inv_eq_mul, mul_comm]

/-- The actual onsets and inequalities used to pass from |t| powers to g. -/
theorem paid_reading (t : ℝ → ℝ) (ht : Tendsto (fun r => t r / g r) τ (𝓝 1)) :
    ∀ᶠ r in τ, 0 < g r ∧ 0 < t r ∧ |t r| ≤ 1 ∧ |t r| ≤ 2*g r := by
  filter_upwards [ht.eventually (gt_mem_nhds (one_lt_two)), ht.eventually (lt_mem_nhds (zero_lt_one)),
    positive_g simple, (shrink simple).eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with r hu hl hg hb
  have hu := (div_lt_iff₀ hg).mp hu
  have hp : 0 < t r := (div_pos_iff_of_pos_right hg).mp hl
  rw [abs_of_pos hp]
  exact ⟨hg,hp,by linarith,hu.le⟩
end
end YM.FVA2.GradedFar
