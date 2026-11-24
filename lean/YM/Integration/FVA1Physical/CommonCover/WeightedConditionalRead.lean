import YM.RG.Bounded

/-! Lift a bound on all complex conditional readings to the weighted sum of
errors of a finite family. One pointwise joint budget pays the entire family,
even when different entries attain their maxima on different configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.FrozenRead
open MeasureTheory RG
open scoped BigOperators

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

local notation "avg(" μ ", " a ", " F ")" =>
  (∫ x, a x ∂μ)⁻¹ • (∫ x, a x • F x ∂μ)

private theorem linear_read (μ : Measure X) (a : X → ℝ) (c : ι → ℂ)
    (F : ι → X → ℂ) (env : ∀ i, Envelope (F i)) :
    avg(μ, a, (fun x => ∑ i, c i * F i x)) = ∑ i, c i * avg(μ, a, (F i)) := by
  classical
  by_cases ha : Integrable a μ
  · have integ (i : ι) : Integrable (fun x => a x • F i x) μ := by
      obtain ⟨C, bound⟩ := (env i).cost
      apply (ha.norm.mul_const C).mono' (ha.aestronglyMeasurable.smul (env i).meas.aestronglyMeasurable)
      filter_upwards with x
      exact (norm_smul (a x) (F i x)).le.trans (mul_le_mul_of_nonneg_left (bound x) (norm_nonneg _))
    simp_rw [Finset.smul_sum, ← mul_smul_comm]
    rw [integral_finsetSum _ (fun i _ => (integ i).const_mul (c i)), Finset.smul_sum]
    simp_rw [integral_const_mul, ← mul_smul_comm]
  · simp [integral_undef ha]

private def phase (z : ℂ) : ℂ := (‖z‖ : ℂ) / z

private theorem phase_norm (z : ℂ) : ‖phase z‖ ≤ 1 := by
  by_cases h : z = 0
  · simp [h, phase]
  simp [phase, Complex.norm_real, h]

private theorem phase_times (z : ℂ) : phase z * z = (‖z‖ : ℂ) := by
  by_cases h : z = 0
  · simp [h, phase]
  exact div_mul_cancel₀ _ h

theorem weighted_conditional_read (μ : Measure X) (a b : X → ℝ) (δ : ℝ)
    (read : ∀ (T : X → ℂ), Envelope T → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖T x‖ ≤ M) →
      ‖avg(μ, a, T) - avg(μ, b, T)‖ ≤ δ * M)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (F : ι → X → ℂ) (env : ∀ i, Envelope (F i))
    (M : ℝ) (hM : 0 ≤ M) (joint : ∀ x, ∑ i, w i * ‖F i x‖ ≤ M) :
    ∑ i, w i * ‖avg(μ, a, (F i)) - avg(μ, b, (F i))‖ ≤ δ * M := by
  classical
  let d := fun i => avg(μ, a, (F i)) - avg(μ, b, (F i))
  let c := fun i => (w i : ℂ) * phase (d i)
  let T := fun x => ∑ i, c i * F i x
  have bound (x : X) : ‖T x‖ ≤ M := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans (joint x))
    rw [norm_mul, show ‖c i‖ = w i * ‖phase (d i)‖ by
      simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i)]]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left (phase_norm _) (hw i)).trans_eq (mul_one _)) (norm_nonneg _)
  have meas : Measurable T := Finset.measurable_sum _ fun i _ => measurable_const.mul (env i).meas
  have estimate := read T ⟨meas, M, bound⟩ M hM bound
  change ‖avg(μ, a, (fun x => ∑ i, c i * F i x)) - avg(μ, b, (fun x => ∑ i, c i * F i x))‖ ≤ _ at estimate
  rw [linear_read μ a c F env, linear_read μ b c F env, ← Finset.sum_sub_distrib] at estimate
  have cost (i : ι) : c i * avg(μ, a, (F i)) - c i * avg(μ, b, (F i)) =
      ((w i * ‖d i‖ : ℝ) : ℂ) := by
    rw [← mul_sub, Complex.ofReal_mul]
    change (w i : ℂ) * phase (d i) * d i = _
    rw [mul_assoc, phase_times]
  simp_rw [cost] at estimate
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (norm_nonneg _))] at estimate
  exact estimate

/-- No count of addresses occurs. A pointwise budget on every finite partial
sum implies summability of the physical discrepancies with the same weights. -/
theorem summable_conditional_read {J : Type*} (μ : Measure X) (a b : X → ℝ) (δ : ℝ)
    (read : ∀ (T : X → ℂ), Envelope T → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖T x‖ ≤ M) →
      ‖avg(μ, a, T) - avg(μ, b, T)‖ ≤ δ * M)
    (w : J → ℝ) (hw : ∀ i, 0 ≤ w i) (F : J → X → ℂ) (env : ∀ i, Envelope (F i))
    (M : ℝ) (hM : 0 ≤ M) (joint : ∀ x (s : Finset J), ∑ i ∈ s, w i * ‖F i x‖ ≤ M) :
    let cost := fun i => w i * ‖avg(μ, a, (F i)) - avg(μ, b, (F i))‖
    Summable cost ∧ ∑' i, cost i ≤ δ * M := by
  classical
  intro cost
  have partialCost (s : Finset J) : ∑ i ∈ s, cost i ≤ δ * M := by
    have h := weighted_conditional_read μ a b δ read (fun i : ↥s => w i) (fun i => hw i)
      (fun i => F i) (fun i => env i) M hM (fun x => (Finset.sum_coe_sort s _).le.trans (joint x s))
    rw [← Finset.sum_coe_sort s cost]
    exact h
  have hs := summable_of_sum_le (f := cost) (fun i => mul_nonneg (hw i) (norm_nonneg _)) partialCost
  exact ⟨hs, hs.tsum_le_of_sum_le partialCost⟩

end YM.Integration.FVA1Physical.FrozenRead
