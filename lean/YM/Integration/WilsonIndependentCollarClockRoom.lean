import YM.Integration.WilsonIndependentCollarPhysicalRates
import YM.Integration.WilsonIndependentCollarPrintIncome

/-! Each fixed polynomial-log bill costs at most one coupling power on the
same actual thermal band, uniformly in the physical regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarClockRoom
open Filter RG Wilson PhysicalNext.Repeat.Legato
open scoped Topology

def threshold (C:ℝ) (k:ℕ) : ℝ :=
  max 1 (2*C^2*2^(2*k)*((2*k+1).factorial:ℝ))

theorem due (C:ℝ) (k:ℕ) {H β:ℝ} (positive:0<H) (late:threshold C k≤Real.log H)
    (thermal:H/2≤β) : C*(1+Real.log H)^k ≤ Real.sqrt β := by
  let y:=Real.log H
  let n:=2*k
  have y₁ : 1≤y := (le_max_left ..).trans late
  have y₀ : 0≤y := by linarith
  have natural : 0<((n+1).factorial:ℝ) := by positivity
  have early : 2*C^2*2^n*((n+1).factorial:ℝ)≤y := (le_max_right ..).trans late
  have c : C^2*2^n≤y/(2*((n+1).factorial:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have mass:C^2*(1+y)^n≤H/2 := by
    calc
      _ ≤ C^2*(2*y)^n := by gcongr; linarith
      _ = (C^2*2^n)*y^n := by rw [mul_pow];ring
      _ ≤ (y/(2*((n+1).factorial:ℝ)))*y^n := mul_le_mul_of_nonneg_right c (pow_nonneg y₀ _)
      _ = (y^(n+1)/((n+1).factorial:ℝ))/2 := by rw [pow_succ];ring
      _ ≤ Real.exp y/2 := by gcongr; exact Real.pow_div_factorial_le_exp y y₀ (n+1)
      _ = _ := by dsimp [y];rw [Real.exp_log positive]
  have sq : (C*(1+Real.log H)^k)^2≤β := by
    rw [mul_pow,←pow_mul,Nat.mul_comm k 2]
    exact mass.trans thermal
  apply (le_abs_self _).trans
  rw [←Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt sq

theorem original {G:Gauge} (R:Run G) (simple:G.Simple) (C:ℝ) (k:ℕ) :
    let A:=R.family.path.levels
    ∀ᶠi:ℕ in atTop,∀β:ℝ,A.clock.hatBeta (i+1)/2≤β →
      C*(1+Real.log (A.clock.hatBeta (i+1)))^k≤( (Real.sqrt β)⁻¹ )⁻¹ := by
  let A:=R.family.path.levels
  have rise:Tendsto A.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have later:=rise.comp (tendsto_add_atTop_nat 1)
  filter_upwards [(Real.tendsto_log_atTop.comp later).eventually_ge_atTop (threshold C k),
    later.eventually_gt_atTop 0] with i tab pos
  intro β band
  rw [inv_inv]
  exact due C k pos tab band

end YM.Integration.WilsonIndependentCollarClockRoom
