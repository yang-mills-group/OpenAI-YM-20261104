import YM.Integration.WilsonLimitConstruction.NativeInheritedRate
import YM.RG01Estimate.Routed

/-! The complete native pruning charge against an admitted positive-order
input debit. The estimate is uniform in cutoff, period and pruning order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPruningRate

open Filter Lattice RG FullQLocal.RawInherited PhysicalNext.Repeat.Legato RG01Estimate
open scoped Topology
variable {G : Gauge}

/-- Every actual regulator coupling power of order at least one is paid by
the raw inverse-monitor contribution on the same physical calendar. -/
theorem regulator_power (R : Run G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m ≤ N → ∀ d : ℝ, 1 ≤ d →
      Pert.Asymptotics.regulatorRun R.family N p m ^ d ≤
        2 * shape R.family.path.levels.clock 0 m := by
  let T := R.family.path.levels
  filter_upwards [(WardBin.bell T hG).eventually_ge_atTop (2 : ℝ),
      NativeInheritedRate.power_le_monitor T hG (by norm_num : 0 < (1/2 : ℝ))]
    with m hHot hPower
  intro N p hm d hd
  have hBand : R.family.path.β N p m ∈ Shoot.band T m :=
    (R.makes.wilson.represents N p m hm).band
  have hhot := WardBin.hot T m
  have hg := (Next.Scheduling.band_gap _ _ hhot (Next.Scheduling.trial_in hBand)).2
  have hβ : 1 ≤ R.family.path.β N p m := by linarith only [hBand.1, hHot]
  have hhalf : (Real.sqrt (T.clock.hatBeta m))⁻¹ ≤ shape T.clock 0 m := by
    rw [Real.rpow_neg hhot.le, ← Real.sqrt_eq_rpow] at hPower
    exact hPower.trans (NativeInheritedRate.monitor_le_shape T m)
  calc
    _ ≤ (Real.sqrt (R.family.path.β N p m))⁻¹ :=
      Real.rpow_le_self_of_le_one (inv_nonneg.mpr (Real.sqrt_nonneg _))
        (inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hβ)) hd
    _ ≤ 2 * (Real.sqrt (T.clock.hatBeta m))⁻¹ := hg
    _ ≤ _ := mul_le_mul_of_nonneg_left hhalf (by norm_num)

/-- Retention times the actual regulated input debit, including the whole
additive spill in the native pruning step. The floor is independent of every
quantity chosen in the displayed universal tail. -/
theorem full_charge (R : Run G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N → ∀ r : ℕ, ∀ d τ c B : ℝ,
      1 ≤ d → 0 ≤ τ → 0 ≤ c → 0 ≤ B →
      Routed.retention R.kit m ≤ c →
      τ ≤ B * Pert.Asymptotics.regulatorRun R.family N p (m+1) ^ d →
      Routed.retention R.kit m * τ + Routed.spill (A:=R.alloy) m r ≤
        (2*c*B+1) * shape R.family.path.levels.clock 0 (m+1) := by
  have shifted : Tendsto (fun m : ℕ => m+1) atTop atTop :=
    tendsto_atTop_mono (f:=id) (fun m => Nat.le_succ m) tendsto_id
  filter_upwards [shifted.eventually (regulator_power R hG),
      NativeInheritedRate.pruning_rates R hG] with m hPower hSpill
  intro N p hm r d τ c B hd hτ hc hB hRetained hDebit
  let rate := shape R.family.path.levels.clock 0 (m+1)
  have hs : Routed.spill (A:=R.alloy) m r ≤ rate := by
    change R.family.path.levels.clock.hatBeta (m+1) ^
      (-((r+1:ℕ)/(2:ℝ))-1/64) ≤ shape R.family.path.levels.clock 0 (m+1)
    exact hSpill.2 r
  calc
    _ ≤ c * τ + rate := add_le_add (mul_le_mul_of_nonneg_right hRetained hτ) hs
    _ ≤ c * (B * (2*rate)) + rate := add_le_add (mul_le_mul_of_nonneg_left
      (hDebit.trans (mul_le_mul_of_nonneg_left (hPower N p hm d hd) hB)) hc) le_rfl
    _ = (2*c*B+1) * rate := by ring

end YM.Integration.WilsonLimitConstruction.FundedPruningRate
end
