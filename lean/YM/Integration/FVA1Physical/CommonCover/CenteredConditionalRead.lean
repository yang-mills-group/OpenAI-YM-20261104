import YM.Integration.FVA1Physical.CommonCover.WeightedConditionalRead

/-! Only the oscillation of a source on the frozen fibre enters. A comparison
of normalized readings with error below one detects the same zero-mass
fibres on both sides, so exterior constants cancel even on those fibres. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.FrozenRead
open MeasureTheory RG
open Filter
open scoped BigOperators Topology

variable {X : Type*} [MeasurableSpace X]
local notation "avg(" μ ", " a ", " F ")" =>
  (∫ x, a x ∂μ)⁻¹ • (∫ x, a x • F x ∂μ)

private theorem const_read (μ : Measure X) (a : X → ℝ) (c : ℂ) :
    avg(μ, a, (fun _ => c)) = if ∫ x, a x ∂μ = 0 then 0 else c := by
  rw [integral_smul_const]
  split_ifs with h
  · simp [h]
  · exact inv_smul_smul₀ h c

private theorem subtract_const (μ : Measure X) (a : X → ℝ) (F : X → ℂ) (env : Envelope F) (c : ℂ) :
    avg(μ, a, (fun x => F x - c)) = avg(μ, a, F) - (if ∫ x, a x ∂μ = 0 then 0 else c) := by
  rw [←const_read μ a c]
  by_cases ha : Integrable a μ
  · obtain ⟨C, bound⟩ := env.cost
    have hi : Integrable (fun x => a x • F x) μ := by
      apply (ha.norm.mul_const C).mono' (ha.aestronglyMeasurable.smul env.meas.aestronglyMeasurable)
      filter_upwards with x
      exact (norm_smul (a x) (F x)).le.trans (mul_le_mul_of_nonneg_left (bound x) (norm_nonneg _))
    simp_rw [smul_sub, integral_sub hi (ha.smul_const c), smul_sub]
  · simp [integral_undef ha]

theorem centered_conditional_read {J : Type*} (μ : Measure X) (a b : X → ℝ) (δ : ℝ) (small : δ < 1)
    (read : ∀ (T : X → ℂ), Envelope T → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖T x‖ ≤ M) →
      ‖avg(μ, a, T) - avg(μ, b, T)‖ ≤ δ * M)
    (w : J → ℝ) (hw : ∀ i, 0 ≤ w i) (F : J → X → ℂ) (env : ∀ i, Envelope (F i)) (c : J → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (osc : ∀ x (s : Finset J), ∑ i ∈ s, w i * ‖F i x - c i‖ ≤ M) :
    let cost := fun i => w i * ‖avg(μ, a, (F i)) - avg(μ, b, (F i))‖
    Summable cost ∧ ∑' i, cost i ≤ δ * M := by
  classical
  have one := read (fun _ => (1 : ℂ)) ⟨measurable_const, 1, fun _ => (norm_one : ‖(1 : ℂ)‖ = 1).le⟩
    1 zero_le_one (fun _ => (norm_one : ‖(1 : ℂ)‖ = 1).le)
  rw [const_read, const_read, mul_one] at one
  have same : (∫ x, a x ∂μ) = 0 ↔ (∫ x, b x ∂μ) = 0 := by
    by_cases ha : (∫ x, a x ∂μ) = 0 <;> by_cases hb : (∫ x, b x ∂μ) = 0 <;>
      simp_all <;> exact (not_le_of_gt small) one
  have moved (i : J) : Envelope (fun x => F i x - c i) := by
    obtain ⟨C, bound⟩ := (env i).cost
    exact ⟨(env i).meas.sub measurable_const, C + ‖c i‖,
      fun x => (norm_sub_le ..).trans (add_le_add (bound x) le_rfl)⟩
  have h := summable_conditional_read μ a b δ read w hw (fun i x => F i x - c i)
    moved M hM osc
  have shift (i : J) :
      avg(μ, a, (fun x => F i x - c i)) - avg(μ, b, (fun x => F i x - c i)) =
      avg(μ, a, (F i)) - avg(μ, b, (F i)) := by
    rw [subtract_const μ a (F i) (env i), subtract_const μ b (F i) (env i), if_congr same rfl rfl]
    abel
  simpa only [shift] using h

/-- A fixed footprint pays the oscillation exponent uniformly in the measured
inverse coupling. The threshold precedes the lattice period and all readouts. -/
theorem small_frozen_footprint (m : ℕ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ β : ℝ in atTop, 0 < β ∧ (m : ℝ) * ((Real.sqrt β)⁻¹)^q < 1/8 := by
  have g : Tendsto (fun β : ℝ => (Real.sqrt β)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have tiny : Tendsto (fun β : ℝ => (m : ℝ) * ((Real.sqrt β)⁻¹)^q) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hq.ne', mul_zero] using ((g.rpow_const (Or.inr hq.le)).const_mul (m : ℝ))
  exact (eventually_gt_atTop 0).and (tiny.eventually_lt_const (by norm_num))

theorem linear_frozen_footprint {t : ℝ} (nonneg : 0 ≤ t) (small : t < 1/8) :
    Real.exp (2*t)-1 < 1 ∧ Real.exp (2*t)-1 ≤ 4*t := by
  have absT : |2*t| = 2*t := abs_of_nonneg (mul_nonneg zero_le_two nonneg)
  have h := Real.abs_exp_sub_one_le (show |2*t| ≤ 1 by rw [absT]; linarith)
  rw [absT] at h
  have h' := (le_abs_self (Real.exp (2*t)-1)).trans h
  constructor <;> linarith

end YM.Integration.FVA1Physical.FrozenRead
