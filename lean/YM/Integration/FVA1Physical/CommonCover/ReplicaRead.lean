import YM.Integration.FVA1Physical.CommonCover.ReplicaActionPrice

/-! A continuous-fibre reading bound for the original and issued laws on
one measure space. Multiplying by the two true normalizations first avoids
paying a separate inverse-denominator error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Replica
open MeasureTheory Filter RG
open scoped Classical BigOperators
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

omit [SFinite μ] in
private theorem weighted {u : X → ℝ} (ui : Integrable u μ) {F : X → ℂ} (env : Envelope F) :
    Integrable (fun x => u x • F x) μ := by
  obtain ⟨M,bd⟩ := env.cost
  apply (ui.norm.mul_const M).mono' (ui.aestronglyMeasurable.smul env.meas.aestronglyMeasurable)
  filter_upwards with x
  change ‖u x • F x‖ ≤ ‖u x‖*M
  exact (norm_smul (u x) (F x)).le.trans (mul_le_mul_of_nonneg_left (bd x) (norm_nonneg _))

private theorem difference_env {F : X → ℂ} (env : Envelope F) : Envelope (fun z:X×X => F z.1-F z.2) := by
  obtain ⟨C,h⟩ := env.cost
  exact ⟨(env.meas.comp measurable_fst).sub (env.meas.comp measurable_snd), C+C,
    fun z => (norm_sub_le ..).trans (add_le_add (h z.1) (h z.2))⟩

omit [SFinite μ] in
private theorem spread {u v : X → ℝ} (ui : Integrable u μ) (vi : Integrable v μ)
    {F : X → ℂ} (env : Envelope F) :
    Integrable (fun z:X×X => cost u v z • (F z.1-F z.2)) (μ.prod μ) :=
  weighted (ui.mul_prod vi) (difference_env env)

private theorem separated {u v : X → ℝ} (ui : Integrable u μ) (vi : Integrable v μ)
    {F : X → ℂ} (env : Envelope F) :
    (∫ z, cost u v z • (F z.1-F z.2) ∂μ.prod μ) =
      (∫y,v y ∂μ) • (∫x,u x • F x ∂μ) - (∫x,u x ∂μ) • (∫y,v y • F y ∂μ) := by
  rw [integral_prod _ (spread ui vi env)]
  have inner (x : X) : (∫y,cost u v (x,y) • (F x-F y) ∂μ) =
      (∫y,v y ∂μ) • (u x • F x) - u x • (∫y,v y • F y ∂μ) := by
    have raw : (∫y,v y • (F x-F y) ∂μ) = (∫y,v y ∂μ) • F x - ∫y,v y • F y ∂μ := by
      simp_rw [smul_sub]; rw [integral_sub (vi.smul_const (F x)) (weighted vi env),integral_smul_const]
    dsimp only [cost]
    simp_rw [mul_smul]; rw [integral_smul,raw,smul_sub,smul_comm (u x)]
  simp_rw [inner]
  have l : Integrable (fun x=>(∫y,v y ∂μ) • (u x • F x)) μ := (weighted ui env).smul (∫y,v y ∂μ)
  have h : Integrable (fun x=>u x • (∫y,v y • F y ∂μ)) μ := ui.smul_const _
  rw [integral_sub l h,integral_smul,integral_smul_const]

/-- The exact two-draw identity for two arbitrary positive normalizations. -/
theorem true_centers {u v : X → ℝ} (ui : Integrable u μ) (vi : Integrable v μ)
    (up : 0<∫x,u x ∂μ) (vp : 0<∫x,v x ∂μ) {F : X → ℂ} (env : Envelope F) :
    (∫ z,(cost u v z-cost v u z) • (F z.1-F z.2) ∂μ.prod μ) =
      (2*(∫x,u x ∂μ)*(∫x,v x ∂μ)) • (FrozenRead.meanOn μ u F-FrozenRead.meanOn μ v F) := by
  simp_rw [sub_smul]
  rw [integral_sub (spread ui vi env) (spread vi ui env),separated ui vi env,separated vi ui env]
  unfold FrozenRead.meanOn
  rw [smul_sub,smul_smul,smul_smul,
    show 2*(∫x,u x ∂μ)*(∫x,v x ∂μ)*(∫x,u x ∂μ)⁻¹ = 2*(∫x,v x ∂μ) by field_simp,
    show 2*(∫x,u x ∂μ)*(∫x,v x ∂μ)*(∫x,v x ∂μ)⁻¹ = 2*(∫x,u x ∂μ) by field_simp,
    mul_smul,mul_smul,two_smul,two_smul]
  abel

omit [SFinite μ] in
theorem cost_times_diameter {B : X×X → ℝ} (bi : Integrable B (μ.prod μ))
    {F : X → ℂ} (env : Envelope F) : Integrable (fun z => B z*‖F z.1-F z.2‖) (μ.prod μ) := by
  have hE := difference_env env
  obtain ⟨C,bc⟩ := hE.cost
  apply (bi.norm.mul_const C).mono' (bi.aestronglyMeasurable.mul hE.meas.norm.aestronglyMeasurable)
  filter_upwards with z
  change ‖B z*‖F z.1-F z.2‖‖ ≤ ‖B z‖*C
  rw [norm_mul,Real.norm_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (bc z) (norm_nonneg _)

/-- Keep the action error and marked oscillation on the *same* pair of fields.
This bound holds off the regular collar as well as on it. -/
theorem reading {k a b r : X → ℝ} (kn : ∀x,0≤k x) (ap : ∀x,0<a x) (bp : ∀x,0<b x)
    (rm : Measurable r) (anchor : ℝ) (same : ∀x,Real.log (a x)-Real.log (b x)=r x+anchor)
    {F : X → ℂ} (env : Envelope F) :
    let u := fun x => k x*a x
    let v := fun x => k x*b x
    Integrable u μ → Integrable v μ → 0<(∫x,u x ∂μ) → 0<(∫x,v x ∂μ) →
      2*(∫x,u x ∂μ)*(∫x,v x ∂μ)*‖FrozenRead.meanOn μ u F-FrozenRead.meanOn μ v F‖ ≤
        ∫z,actionBill u v r z*‖F z.1-F z.2‖ ∂μ.prod μ := by
  intro u v ui vi up vp
  have un (x) : 0≤u x := mul_nonneg (kn x) (ap x).le
  have vn (x) : 0≤v x := mul_nonneg (kn x) (bp x).le
  have iB := integrable_bill ui vi un vn rm
  have integr := cost_times_diameter iB env
  have normEq := congrArg norm (true_centers ui vi up vp env)
  rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤2*(∫x,u x ∂μ)*(∫x,v x ∂μ))] at normEq
  rw [←normEq]
  apply norm_integral_le_of_norm_le integr
  apply Eventually.of_forall; intro z
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (centered_determinant k a b r kn ap bp anchor same z) (norm_nonneg _)

end YM.Integration.FVA1Physical.Replica
