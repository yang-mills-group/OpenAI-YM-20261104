import YM.Integration.FVA1Physical.Wilson.RelativeTilt

/-! Perturb a normalized finite-dimensional kernel by a uniformly controlled log
tilt, without any quantitative lower bound on the volume-dependent partition function. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set
open scoped Classical
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem log_tilt (K Q P : X→ℝ) (μ : Measure X) [IsFiniteMeasure μ] (hmass : 0 < μ Set.univ)
    (kpos : ∀ x, 0 < K x) (pos : ∀ x, 0 < Q x) (kmeas : Measurable K)
    (ia : Integrable (fun x=>K x*Q x) μ) (hP : AEMeasurable P μ)
    (center δ : ℝ) (hδ : 0 ≤ δ) (relative : ∀ᵐ x ∂μ, |Real.log (Q x)-P x-center| ≤ δ)
    (F : X→E) (hF : AEStronglyMeasurable F μ) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ M) :
    ‖patchMean μ (fun x=>K x*Q x) F - patchMean μ (fun x=> K x*Real.exp (P x)) F‖ ≤ (Real.exp (2*δ)-1)*M := by
  let a := fun U=> K U*Q U
  let c₀ := Real.exp center
  let b₀ := fun U=>K U*Real.exp (P U)
  let b := fun U=>c₀*b₀ U
  let l := Real.exp (-δ)
  let u := Real.exp δ
  have Cp : 0<c₀ := Real.exp_pos _
  have lp : 0<l := Real.exp_pos _
  have ul : l ≤ u := Real.exp_le_exp.mpr (by linarith)
  have bpos U : 0<b U := mul_pos Cp (mul_pos (kpos U) (Real.exp_pos _))
  have bmeas : AEMeasurable b μ :=
    aemeasurable_const.mul (kmeas.aemeasurable.mul (Real.continuous_exp.measurable.comp_aemeasurable hP))
  have band : ∀ᵐ U ∂μ, l*b U ≤ a U ∧ a U ≤ u*b U := by
    filter_upwards [relative] with U hu
    have id : Real.exp (Real.log (Q U)-P U-center)*b U=a U := by
      dsimp only [b,b₀,a,c₀]
      rw [show Real.exp (Real.log (Q U)-P U-center) * (Real.exp center * (K U*Real.exp (P U))) =
        K U*Real.exp ((Real.log (Q U)-P U-center)+center+P U) by rw [Real.exp_add,Real.exp_add];ring]
      rw [show (Real.log (Q U)-P U-center)+center+P U=Real.log (Q U) by ring,Real.exp_log (pos U)]
    rw [←id]
    exact ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp hu).1) (bpos U).le,
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp hu).2) (bpos U).le⟩
  have ib : Integrable b μ := by
    apply (ia.const_mul l⁻¹).mono' bmeas.aestronglyMeasurable
    filter_upwards [band] with U hu
    rw [Real.norm_of_nonneg (bpos U).le]
    simpa only [div_eq_inv_mul] using (le_div_iff₀ lp).2 (by simpa only [mul_comm (b U) l] using hu.1)
  have mass : 0<∫ U,b U ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun U=>(bpos U).le) ib).2
    simpa only [show Function.support b = Set.univ from Set.eq_univ_of_forall fun U=>(bpos U).ne'] using hmass
  have cost := relative_tilt μ a b F ia ib (.of_forall fun U=>(bpos U).le) mass hF hM hbound lp ul band
  change ‖patchMean μ a F - patchMean μ (fun x=>c₀*b₀ x) F‖ ≤ (u-l)/l*M at cost
  rw [patchMean_scale μ b₀ F Cp.ne'] at cost
  have rate : (u-l)/l = Real.exp (2*δ)-1 := by
    dsimp only [u,l]
    rw [sub_div,div_self (Real.exp_pos _).ne',←Real.exp_sub,show δ- -δ=2*δ by ring]
  rw [rate] at cost
  exact cost

end YM.Integration.FVA1Physical.Wilson
