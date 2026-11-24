import YM.Integration.FVA1Physical.Marked.MeanLedger

/-! Stability of a normalized interacting reading under a relative error in its
density. Neither individual vacuum normalization requires a quantitative lower bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open MeasureTheory Filter Set
open scoped Classical
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (a b : X→ℝ) (F : X→E)

def patchMean (a : X→ℝ) (F : X→E) := (∫ x,a x ∂μ)⁻¹ • ∫ x,a x • F x ∂μ

theorem patchMean_scale {c : ℝ} (hc : c ≠ 0) :
    patchMean μ (fun x => c*a x) F = patchMean μ a F := by
  unfold patchMean
  simp_rw [mul_smul]
  rw [integral_smul,integral_const_mul,smul_smul]
  congr 1
  rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ hc,mul_one]

theorem relative_tilt (ia : Integrable a μ) (ib : Integrable b μ)
    (b₀ : ∀ᵐ x ∂μ, 0 ≤ b x) (mass : 0<∫ x, b x ∂μ)
    (hm : AEStronglyMeasurable F μ) {M : ℝ} (hM : 0 ≤ M) (test : ∀ᵐ x ∂μ, ‖F x‖ ≤ M)
    {l u : ℝ} (hl : 0<l) (hlh : l ≤ u)
    (band : ∀ᵐ x ∂μ, l*b x ≤ a x ∧ a x ≤ u*b x) :
    ‖patchMean μ a F - patchMean μ b F‖ ≤ (u-l)/l*M := by
  let A := ∫ x,a x ∂μ
  let B := ∫ x,b x ∂μ
  have low : l*B ≤ A := by
    simpa only [A,B,integral_const_mul] using integral_mono_ae (ib.const_mul l) ia (band.mono fun _ h=>h.1)
  have high : A ≤ u*B := by
    simpa only [A,B,integral_const_mul] using integral_mono_ae ia (ib.const_mul u) (band.mono fun _ h=>h.2)
  have hA : 0<A := (mul_pos hl mass).trans_le low
  have ratioL := (le_div_iff₀ mass).mpr low
  have ratioU := (div_le_iff₀ mass).mpr high
  have weighted (s : X→ℝ) (hs : Integrable s μ) : Integrable (fun x=>s x • F x) μ := by
    apply (hs.norm.mul_const M).mono' (hs.aestronglyMeasurable.smul hm)
    filter_upwards [test] with x hx
    change ‖s x • F x‖ ≤ ‖s x‖ * M
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  have point : ∀ᵐ x ∂μ, ‖(a x - A/B*b x) • F x‖ ≤ ((u-l)*M)*b x := by
    filter_upwards [b₀,band,test] with x hb hx hF
    have lower := mul_le_mul_of_nonneg_right ratioL hb
    have upper := mul_le_mul_of_nonneg_right ratioU hb
    have err : |a x - A/B*b x| ≤ (u-l)*b x := by
      apply abs_le.mpr
      rw [sub_mul]
      constructor <;> linarith only [lower,upper,hx.1,hx.2]
    rw [norm_smul,Real.norm_eq_abs]
    refine (mul_le_mul err hF (norm_nonneg _) (mul_nonneg (sub_nonneg.mpr hlh) hb)).trans_eq ?_
    ring
  have h := norm_integral_le_of_norm_le ((ib.const_mul ((u-l)*M))) point
  rw [integral_const_mul] at h
  have identity : patchMean μ a F - patchMean μ b F =
      A⁻¹ • ∫ x,(a x - A/B*b x) • F x ∂μ := by
    simp only [sub_smul,mul_smul]
    have im : Integrable (fun x=> (A/B) • (b x • F x)) μ := Integrable.smul (A/B) (weighted b ib)
    rw [integral_sub (weighted a ia) im, integral_smul,smul_sub,smul_smul]
    change A⁻¹ • _ - B⁻¹ • _ = A⁻¹ • _ - (A⁻¹*(A/B)) • _
    rw [show A⁻¹*(A/B)=B⁻¹ by field_simp]
  rw [identity,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hA.le)]
  apply (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hA.le)).trans
  calc
    A⁻¹ * ((u-l)*M*B) = (B/A)*((u-l)*M) := by ring
    _ ≤ (1/l)*((u-l)*M) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (sub_nonneg.mpr hlh) hM)
      apply (div_le_div_iff₀ hA hl).mpr
      simpa only [one_mul,mul_comm B l] using low
    _ = _ := by ring

end YM.Integration.FVA1Physical.Wilson
