import Mathlib

/-! A charge for the inherited marked error at the actual coupling. Center
before pricing the signed integrand. The price uses the two existing positive
vacuum weights and accepts unbounded log changes with finite weighted cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OlderPrice
open MeasureTheory Filter
open scoped ComplexConjugate

private theorem sub_le_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b-a ≤ b*(Real.log b-Real.log a) := by
  have h := Real.add_one_le_exp (Real.log a - Real.log b)
  rw [Real.exp_sub, Real.exp_log ha, Real.exp_log hb] at h
  have bound := (le_div_iff₀ hb).mp h
  linarith only [bound, mul_comm (Real.log a - Real.log b + 1) b]

theorem mass_change {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a-b| ≤ max a b * |Real.log a - Real.log b| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab),
        abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hab)), max_eq_right hab, neg_sub, neg_sub]
    exact sub_le_log ha hb
  · rw [abs_of_nonneg (sub_nonneg.mpr hba),
        abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hba)), max_eq_left hba]
    exact sub_le_log hb ha

/-- Subtract the *same* target mixed coefficient multiplied by the quiet
error. If the two normalized insertions both equal the target, the charge
therefore vanishes at any vacuum ratio. -/
theorem centered_coefficient {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (u v q : ℂ) :
    ‖(a:ℂ)*u - (b:ℂ)*v - ((a-b:ℝ):ℂ)*q‖ ≤
      a*‖u-v‖ + max a b * |Real.log a-Real.log b| * ‖v-q‖ := by
  have split : (a:ℂ)*u - (b:ℂ)*v - ((a-b:ℝ):ℂ)*q =
      (a:ℂ)*(u-v) + ((a-b:ℝ):ℂ)*(v-q) := by push_cast; ring
  rw [split]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos ha]
  exact add_le_add_right (mul_le_mul_of_nonneg_right (mass_change ha hb) (norm_nonneg (v-q))) _

variable {X : Type*} [MeasurableSpace X]

/-- Localize the signed discrepancy on the very same mask and charge every
point with its common nonnegative kernel. Integrability is required only
for the displayed positive price. -/
theorem centered_window (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (κ a b : X → ℝ) (u v : X → ℂ) (q : ℂ)
    (admitted : ∀ x ∈ A, 0 ≤ κ x ∧ 0 < a x ∧ 0 < b x)
    (finite : IntegrableOn (fun x => κ x * (a x*‖u x-v x‖ +
      max (a x) (b x) * |Real.log (a x)-Real.log (b x)| * ‖v x-q‖)) A μ) :
    ‖∫ x in A, (κ x:ℂ) * ((a x:ℂ)*u x - (b x:ℂ)*v x -
         ((a x-b x:ℝ):ℂ)*q) ∂μ‖ ≤
      ∫ x in A, κ x * (a x*‖u x-v x‖ +
        max (a x) (b x) * |Real.log (a x)-Real.log (b x)| * ‖v x-q‖) ∂μ := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) finite
  filter_upwards [ae_restrict_mem hA] with x hx
  obtain ⟨hk,ha,hb⟩ := admitted x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left (centered_coefficient ha hb (u x) (v x) q) hk

end YM.Integration.FVA1Physical.OlderPrice
