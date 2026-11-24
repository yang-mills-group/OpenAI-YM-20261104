import YM.Marker.Weight

/-! Independent linear tests on all admissible marker modes, and restoration of the
actual vacuum before integration. The bound has no factor counting modes. -/

namespace YM.Integration.FVA1Physical

open Filter MeasureTheory
open scoped BigOperators

variable {I : Type*} [DecidableEq I] {B : Marker.Census I}

/-- Independently choose a coefficient for each admitted joint marker mode. -/
noncomputable def modeTest (u : B.Mode → ℂ) (X : Marker.Poly B) : ℂ :=
  ∑ m, u m * X.part m

theorem norm_modeTest_le_price (u : B.Mode → ℂ) (X : Marker.Poly B)
    (hu : ∀ m, ‖u m‖ ≤ 1) :
    ‖modeTest u X‖ ≤ Marker.Poly.price (fun _ => 1) X := by
  calc
    ‖modeTest u X‖ ≤ ∑ m, ‖u m * X.part m‖ := norm_sum_le ..
    _ ≤ ∑ m, ‖X.part m‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hu m)
    _ = Marker.Poly.price (fun _ => 1) X := by
      simp [Marker.Poly.price, Marker.Poly.toll]

theorem modeTest_real_smul (u : B.Mode → ℂ) (q : ℝ) (X : Marker.Poly B) :
    modeTest u (q • X) = (q : ℂ) * modeTest u X := by
  change ∑ m, u m * ((q : ℂ) * X.part m) = (q : ℂ) * ∑ m, u m * X.part m
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => mul_left_comm _ _ _

/-- Undo conditional division by the actual positive vacuum, leaving the error
proportional to that same vacuum. This works simultaneously for all modes. -/
theorem unnormalized_modeTest_bound (u : B.Mode → ℂ) (X Y : Marker.Poly B)
    {q ε : ℝ} (hq : 0 < q) (hu : ∀ m, ‖u m‖ ≤ 1)
    (hp : Marker.Poly.price (fun _ => 1) (q⁻¹ • X - Y) ≤ ε) :
    ‖modeTest u (X - q • Y)‖ ≤ q * ε := by
  have he : X - q • Y = q • (q⁻¹ • X - Y) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
  rw [he, modeTest_real_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le]
  exact mul_le_mul_of_nonneg_left ((norm_modeTest_le_price u _ hu).trans hp) hq.le

/-- A Haar integral of an unnormalized error on a measurable sector, divided
by the exact partition, inherits its local bound. -/
theorem restricted_partition_bound {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (q : S → ℝ) (f : S → ℂ) {healthy : Set S} (hs : MeasurableSet healthy)
    {Z ε : ℝ} (hZ : 0 < Z) (hε : 0 ≤ ε)
    (hq : Integrable q μ) (hpos : ∀ v, 0 ≤ q v) (hpartition : ∫ v, q v ∂μ = Z)
    (herr : ∀ v ∈ healthy, ‖f v‖ ≤ q v * ε) :
    (AEStronglyMeasurable f (μ.restrict healthy) →
      IntegrableOn f healthy μ ∧ (∫ v in healthy, ‖f v‖ ∂μ) / Z ≤ ε) ∧
      ‖(∫ v in healthy, f v ∂μ) / (Z : ℂ)‖ ≤ ε := by
  have hp : ∀ᵐ v ∂μ.restrict healthy, ‖f v‖ ≤ q v * ε :=
    (ae_restrict_mem hs).mono fun v hv => herr v hv
  have hi : Integrable (fun v => q v * ε) (μ.restrict healthy) := hq.restrict.mul_const ε
  have hpay : (∫ v in healthy, q v * ε ∂μ) ≤ ε * Z := calc
    _ = (∫ v in healthy, q v ∂μ) * ε := integral_mul_const ..
    _ ≤ Z * ε := mul_le_mul_of_nonneg_right
      ((setIntegral_le_integral hq (Eventually.of_forall hpos)).trans_eq hpartition) hε
    _ = ε * Z := mul_comm _ _
  constructor
  · intro h
    have hf := hi.mono' h hp
    exact ⟨hf, (div_le_iff₀ hZ).mpr ((integral_mono_ae hf.norm hi hp).trans hpay)⟩
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le, div_le_iff₀ hZ]
    exact (norm_integral_le_of_norm_le hi hp).trans hpay

end YM.Integration.FVA1Physical
