import YM.Integration.LocalComparisonInterface
import YM.IterationFour.Running

/-!
The scalar smallness needed for the forced-cover estimate is paid by the
existing actual schedule. No new delay, family, or forced receipt is chosen.
The reporting threshold depends on the number of marked slots and is
uniform in the perturbative power, cutoff, and period.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison

open Filter Lattice Wilson RG
open scoped Topology

variable {G : Gauge}

/-- The schedule's actual divided forced allowance tends to zero. -/
theorem forcedDivisor_tendsto (C : Family G) (hG : G.Simple) :
    Tendsto (forcedDivisor C) atTop (𝓝 0) := by
  change Tendsto (fun m => Real.sqrt (C.path.levels.clock.forcedAllowance m)) atTop (𝓝 0)
  simpa only [pow_zero, one_mul] using WardBin.pale C.path.levels hG 0

/-- At late actual stages, the native vacuum allowance plus every marked
power budget fits the compulsory-cover cap. The same threshold works for
all orders, cutoffs, and periods, using the original actual fine coupling. -/
theorem actual_forced_smallness (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (marks : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N → ∀ order : ℕ,
      C.path.levels.clock.forcedAllowance m + (marks : ℝ) *
        (forcedDivisor C m *
          Pert.Asymptotics.regulatorRun C N period (m + 1) ^ order) ≤ 1 := by
  have hRoot := forcedDivisor_tendsto C hG
  have hTotal : Tendsto (fun m : ℕ =>
      (forcedDivisor C m)^2 + (marks : ℝ) * forcedDivisor C m) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] using
      (hRoot.pow 2).add (hRoot.const_mul (marks : ℝ))
  obtain ⟨start, hStart⟩ := eventually_atTop.mp
    (IterationFour.Currency.g_small hG hC 1 zero_lt_one)
  filter_upwards [hTotal.eventually (gt_mem_nhds zero_lt_one),
    eventually_ge_atTop start] with m hTotal hm N period hN order
  have hFine : m + 1 ≤ N := by omega
  have hCoupling : 0 < Pert.Asymptotics.regulatorRun C N period (m + 1) :=
    IterationFour.Currency.g_pos hC N period (m + 1) hFine
  have hCouplingSmall : Pert.Asymptotics.regulatorRun C N period (m + 1) < 1 :=
    hStart (m + 1) (by omega) N period hFine
  have hPower : Pert.Asymptotics.regulatorRun C N period (m + 1)^order ≤ 1 :=
    pow_le_one₀ hCoupling.le hCouplingSmall.le
  have hDivisor : 0 ≤ forcedDivisor C m := Real.sqrt_nonneg _
  have hSquare : (forcedDivisor C m)^2 = C.path.levels.clock.forcedAllowance m :=
    Real.sq_sqrt (Real.exp_pos _).le
  calc
    _ ≤ C.path.levels.clock.forcedAllowance m + (marks : ℝ) * forcedDivisor C m :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right hDivisor hPower) (Nat.cast_nonneg _))
    _ = (forcedDivisor C m)^2 + (marks : ℝ) * forcedDivisor C m := by rw [hSquare]
    _ ≤ 1 := hTotal.le

end YM.Integration.LocalComparison
