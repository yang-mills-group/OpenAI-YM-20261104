import YM.Integration.WilsonOriginalTemperatureDecay

/-! Make the fixed power of logarithmic scale in the genuine spectral
estimate payable at the actual signed Wilson thermometer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalDiscCurrency
open Filter Lattice Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology

theorem original {G : Gauge} {u : ℝ → ℝ} (clock : Coupling G u) (A : ℝ) (hA : 0 ≤ A) (p : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail, A*|LogV r|^p ≤ Real.exp (D*(u r)⁻¹^4) := by
  let b := |G.slopeConstant⁻¹|+1
  have hb : 0 < b := by dsimp [b]; positivity
  have age := clock.running.abs.eventually (ge_mem_nhds (show |G.slopeConstant⁻¹| < b by dsimp [b]; linarith))
  have cold := WilsonOriginalTemperatureDecay.original clock
  refine ⟨A+p*b,by positivity,?_⟩
  filter_upwards [clock.positive,(tendsto_order.mp cold).2 1 zero_lt_one,age] with r hu hu1 bounded
  have year : |LogV r| *(u r)^2 ≤ b := by simpa only [abs_mul,abs_of_nonneg (sq_nonneg (u r))] using bounded
  have bar : |LogV r| ≤ b*((u r)⁻¹)^2 := by
    rw [inv_pow,← div_eq_mul_inv,le_div_iff₀ (sq_pos_of_pos hu)]
    exact year
  have bigger : 1 ≤ (u r)⁻¹ := (one_le_inv₀ hu).mpr hu1.le
  have edge : 1 ≤ (u r)⁻¹^4 := one_le_pow₀ bigger
  have y : |LogV r| ≤ b*(u r)⁻¹^4 :=
    bar.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ bigger (by norm_num : 2 ≤ 4)) hb.le)
  have first : A ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
  have second : |LogV r| ≤ Real.exp |LogV r| := by linarith [Real.add_one_le_exp |LogV r|]
  calc
    _ ≤ Real.exp A * (Real.exp |LogV r|)^p := by gcongr
    _ = Real.exp (A + p*|LogV r|) := by rw [Real.exp_add,Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [add_mul,mul_assoc]
      exact add_le_add (le_mul_of_one_le_right hA edge) (mul_le_mul_of_nonneg_left y (Nat.cast_nonneg _))

end YM.Integration.WilsonOriginalPhysicalDiscCurrency
