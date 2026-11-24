import YM.Pressure.Seeds

/-! The cutoff actually used by the marked wallet grows quadratically in the
logarithm of the reference inverse coupling. Its reserved exponential tail
pays every prescribed inverse power, with an explicit onset. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Filter Pressure
open scoped Topology

theorem till_inverse_power {v β P : ℝ} (hv : 0 < v) (hβ : 1 ≤ β)
    (hP : 100000*P ≤ v * Real.log β) :
    Real.exp (-(v * (Stores.till β + 1 : ℕ))) ≤ β ^ (-P) := by
  have hlog := Real.log_nonneg hβ
  have hrad : (Real.log β)^2 ≤ (radiusB β : ℝ) := Nat.le_ceil _
  have hcut : radiusB β ≤ 100000*(Stores.till β+1) :=
    (Nat.lt_mul_div_succ (radiusB β) (show 0 < 100000 by decide)).le
  have hcast : (radiusB β : ℝ) ≤ 100000 * (Stores.till β+1 : ℕ) := by exact_mod_cast hcut
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hβ)]
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hP hlog
  have h₂ := mul_le_mul_of_nonneg_left (hrad.trans hcast) hv.le
  nlinarith

theorem eventual_till_inverse_power {v : ℝ} (hv : 0 < v) (P : ℝ) :
    ∀ᶠ β : ℝ in atTop, Real.exp (-(v * (Stores.till β+1 : ℕ))) ≤ β ^ (-P) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (100000*P/v)] with β hβ hlog
  exact till_inverse_power hv hβ ((div_le_iff₀ hv).mp hlog |>.trans_eq (mul_comm _ _))

end YM.Integration.FVA1Physical.Marked
