import YM.Integration.WilsonMatrixTicketLanesReportedProfiles
import YM.RG16.Unmasked.Pace
import YM.Pert.Asymptotics.RawAxis

/-! Every paid exponential mesh error on the superlogarithmic reporting clock costs arbitrarily little of the true Wilson coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedCurrency
open Filter Real PhysicalNext.Repeat.Legato
open scoped Topology Classical
variable {G : Gauge} (R : Run G)
local notation "Λ" => RG16.Lambda R.family.path.levels

/-- The authentic represented temperature gives this pointwise lower bound at every later regulator and period. -/
theorem clock (m N p q : ℕ) (h : m ≤ N) :
    exp (-(q:ℝ) * Λ m) ≤ Pert.Asymptotics.regulatorRun R.family N p m ^ q := by
  let b := R.family.path.levels.clock.hatBeta m
  let actual := R.family.path.β N p m
  have hb : 0 < b := zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have band := (R.makes.wilson.represents N p m h).band
  have ha : 0 < actual := (half_pos hb).trans_le band.1
  have high : actual ≤ exp (Λ m) := calc
    actual ≤ 2*b := band.2
    _ ≤ exp 2*b := mul_le_mul_of_nonneg_right ((by norm_num : (2:ℝ) ≤ 2+1).trans (Real.add_one_le_exp 2)) hb.le
    _ = exp (Λ m) := by rw [RG16.Lambda,Real.exp_add,Real.exp_log hb]
  have one : 1 ≤ exp (Λ m) := Real.one_le_exp (RG16.Literal.lambda_pos R.family m).le
  have root : sqrt actual ≤ exp (Λ m) := (Real.sqrt_le_iff).2 ⟨(exp_pos _).le, high.trans (by nlinarith only [one])⟩
  have base : exp (-(Λ m)) ≤ (sqrt actual)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.sqrt_pos.2 ha) root
  rw [show -(q:ℝ)*Λ m = (q:ℝ)*(-(Λ m)) by ring,Real.exp_nat_mul]
  exact pow_le_pow_left₀ (exp_pos _).le base q

/-- Constants and order are fixed before all cutoff pairs. A mesh gap at least Λᶜ with c>1 pays every requested power. -/
theorem paid (simple : G.Simple) {c κ C ε : ℝ} (hc : 1 < c) (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε) (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ θ : ℝ, (Λ m)^c ≤ θ → ∀ N p : ℕ, m ≤ N →
      C * exp (-κ * θ) ≤ ε * Pert.Asymptotics.regulatorRun R.family N p m ^ q := by
  have grows := RG16.Literal.lambda_leads R.family simple
  have gain := (tendsto_rpow_atTop (sub_pos.mpr hc)).comp grows
  have free : Tendsto (fun m : ℕ => C*exp (-(Λ m))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp grows)).const_mul C)
  filter_upwards [gain.eventually_ge_atTop (((q:ℝ)+1)/κ),free.eventually (gt_mem_nhds hε)] with m hm charge
  intro θ hθ N p h
  have enough : (q:ℝ)+1 ≤ κ * (Λ m)^(c-1) := by simpa only [Function.comp_apply,mul_comm] using (div_le_iff₀ hκ).mp hm
  have issued : ((q:ℝ)+1)*Λ m ≤ κ * (Λ m)^c := calc
    _ ≤ (κ*(Λ m)^(c-1))*Λ m := mul_le_mul_of_nonneg_right enough (RG16.Literal.lambda_pos R.family m).le
    _ = _ := by rw [mul_assoc,←Real.rpow_add_one (RG16.Literal.lambda_pos R.family m).ne',sub_add_cancel]
  have coupon : exp (-κ*θ) ≤ exp (-(Λ m)) * exp (-(q:ℝ)*Λ m) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [issued, mul_le_mul_of_nonneg_left hθ hκ.le]
  calc C*exp (-κ*θ) ≤ (C*exp (-(Λ m)))*exp (-(q:ℝ)*Λ m) := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left coupon hC
    _ ≤ ε * Pert.Asymptotics.regulatorRun R.family N p m ^ q := mul_le_mul charge.le (clock R m N p q h) (exp_pos _).le hε.le

end YM.Integration.WilsonMatrixTicketLanesReportedCurrency
