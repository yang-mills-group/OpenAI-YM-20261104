import YM.Integration.WilsonMeasuredOwnerReserve
import YM.Integration.WilsonSingleHardStep

/-! The original clock funds arbitrarily small raw one-marker invoices before
the physical positions, source, and cutoffs are read. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSingleHardRadius
open Function Finset Filter Lattice Wilson RG QuadraticLocal PhysicalNext PhysicalNext.Repeat Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open AnalyticBridge VerifiedReset QuadraticLocal.Advent
open scoped Classical
variable {G:Gauge} (R:Run G)
local notation "β" j:max => R.alloy.B.a.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

theorem prices (simple:G.Simple) (p:ℕ) {ε:ℝ} (pos:0<ε) :
    ∃ u:ℕ, ∀ j≥u, κ j ≤ 1/2 ∧ κ j ≤ ε/(β j)^(p+1) := by
  let A:=R.family.path.levels
  let δ:=min ε (1/2)
  have dp:0<δ:=lt_min pos (by norm_num)
  have hδ:∀ᶠ j:ℕ in atTop, (A.clock.hatBeta j)^(2*(p+1))*A.clock.forcedAllowance j ≤ δ^2 :=
    (RG01.Physical.shrink simple A (2*(p+1))).eventually_le_const (by positivity)
  apply eventually_atTop.1
  filter_upwards [hδ] with j cash
  have wh : 1 ≤ β j := (R.alloy.B.a.fits.delayed j).le
  have hβ : 0<β j:=by linarith
  have hk : 0≤κ j:=Real.sqrt_nonneg _
  have squared : (κ j)^2=A.clock.forcedAllowance j := Real.sq_sqrt (Real.exp_pos _).le
  have twice : (κ j*(β j)^(p+1))^2 ≤ δ^2 := by
    rw [mul_pow,squared,←pow_mul,Nat.mul_comm (p+1) 2,mul_comm]
    exact cash
  have bound: κ j*(β j)^(p+1) ≤ δ := by nlinarith only [twice,dp.le]
  have room : κ j ≤ δ :=
    (le_mul_of_one_le_right hk (one_le_pow₀ wh)).trans bound
  exact ⟨room.trans (min_le_right ..),(le_div_iff₀ (pow_pos hβ _)).2 (bound.trans (min_le_left ..))⟩

noncomputable def start (simple:G.Simple) (p:ℕ) {ε:ℝ} (pos:0<ε) : ℕ :=
  Classical.choose (prices R simple p pos)

theorem cash (simple:G.Simple) (p:ℕ) {ε:ℝ} (pos:0<ε) {j:ℕ}
    (ready:start R simple p pos ≤ j) :
    κ j ≤ 1/2 ∧ κ j ≤ ε/(β j)^(p+1) := Classical.choose_spec (prices R simple p pos) j ready

end YM.Integration.WilsonSingleHardRadius
